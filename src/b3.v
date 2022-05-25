(* These exercises require inductive proofs. *)
(* Now that you have some experience with Coq, 
   you can use 'auto' tactic to avoid solving simple subgoals manually. *)

Require Import b1.
Require Import b2.
Require Import List.
Import ListNotations. 

Section NatDict'Proofs.
  Context {V: Type}.

 Lemma n_eq_or_neq (n n': nat): (n=n')\/(n<>n').
  Proof.
  pattern n, n'.
  apply (nat_double_ind).
  {
    intros n0.
    destruct n0.
    auto.
    auto.
  }
  {
    intros n0.
    auto.
  }
  {
    intros n0 m.
    intros h.
    destruct h.
    auto.
    auto.
  }
Qed.


Lemma noeq_impl_nat_eq_false (n1:nat) (n2:nat) : n1 <> n2 -> nat_eq n1 n2 = false.
    Proof.
      intros.
      remember H as H'.
      remember (nat_eq_neg_spec n1 n2) as nat_eq_neg.
      unfold iff in nat_eq_neg.
      destruct nat_eq_neg as (nat_eq_neg_l & nat_eq_neg_r).
      (*Reset Heqn1.*)
      auto.
    Qed.
    

  (* Prove that 'remove' operation actually removes a key. *)
  (* The list inside nat_dict_list consists of pairs.
     To extract components of such list's head, 
     either perform pattern matching in 'induction' tactics
     or directly 'destruct' the element of nat*V type. *)
  Lemma removed_not_contained (d: @nat_dict_list V) (n: nat):
    contains'' (remove'' d n) n = false.
  Proof.
  induction d.
  auto.

(*  unfold contains''.
  unfold get''.*)
  destruct a.
  destruct (n_eq_or_neq n n0).
  {
    apply eq_implies_nat_eq in H.
    simpl.
    rewrite H.
    auto.
  }
  apply noeq_impl_nat_eq_false in H.
  simpl.
  rewrite H.
  simpl.
  rewrite H.
  
(*rewrite Heqaaa.
  pattern (remove'' d n), n in Heqaaa.
   
  pattern (remove'' d n), n.
  fold (@contains'' V).
  fold ((contains'' (remove'' d n) n)).
  inversion (get'' (remove'' d n) n).
  
  fold (@contains'' V).
  
  unfold contains'' in IHd.
  
  fold (@contains'' V) n (remove'' d n).
  IHd.
  unfold contains'' in IHd.
  red in IHd.
  rewrite IHd.
  destruct IHd.
  auto.
*)
  

  
  
  
Admitted.

  (* Define a mapping function similar to one defined for regular lists.
     It should replace values stored in dict but keep them under the same keys. *)
  Fixpoint map'' {W: Type} (f: V -> W) (d: @nat_dict_list V): @nat_dict_list W :=
      (* place your code here *)
      match d with
      | nil => nil
      | cons (k, v) t => cons (k, f v) (map'' f t)
      end.

      
  (* Prove that a value stored in a mapped dict 
     requires a corresponding value stored in an original dict. *)
  Lemma dict_map_get {W: Type} (m: V -> W) (d: @nat_dict_list V):
    forall n w,
      (get'' (map'' m d) n = Some w) <->
      (exists v, get'' d n = Some v /\ m v = w).
  Proof.
  unfold iff.
  split.
  {
    intros.
    induction d as [| a l ih].
    {unfold get''.
      simpl in H.
      inversion H.
    }
    destruct a.
    destruct (n_eq_or_neq n n0).
    {
      rewrite H0.
      simpl.
      exists v.
      (*eapply ex_intro.*)
      rewrite nat_eq_refl.
      split.
      {reflexivity. }
      rewrite H0 in H.
      simpl in H.
      rewrite nat_eq_refl in H.
      inversion H.
      reflexivity.
    }
    simpl in H.
    remember H0 as H0'.
    remember (nat_eq_neg_spec n n0) as nat_eq_neg.
    unfold iff in nat_eq_neg.
    destruct nat_eq_neg as (nat_eq_neg_l & nat_eq_neg_r).
    (*Reset Heqn1.*)
    remember (nat_eq_neg_r H0') as H1.
    rewrite H1 in H.
    apply ih in H.

    unfold get''.
    simpl.
    rewrite H1.
    auto.
    }

    intros.
    destruct H as (v & H).
    destruct H as (H1 & H2).
    induction d as [| a l ih].
    {
      simpl in H1.
      inversion H1.
    }
    destruct a.
    destruct (n_eq_or_neq n n0).
    {
    apply eq_implies_nat_eq in H.
    simpl in H1.
    rewrite H in H1.
    simpl.
    rewrite H.
    inversion H1.
    destruct H2.
    reflexivity.
    }
    apply noeq_impl_nat_eq_false in H.
    simpl in H1.
    rewrite H in H1.
    simpl.
    rewrite H.
    auto.
Qed.
    
    




  (* Implement a filtering function. 
     The result should contain only those keys whose values satisfy the predicate;
     in this case they remain unchanged. *)
  Fixpoint filter'' {U: Type} (f: U -> bool) (d: @nat_dict_list U): @nat_dict_list U :=
      (* place your code here *)
      match d with
      | nil => nil
      | cons (k, v) t => if (f v) then cons (k, v) (filter'' f t) else (filter'' f t)
      end.

  

(*...*)

  (* Prove that the result of filtering is actually filtered *)
  Lemma filter_elem (f: V -> bool) (d: @nat_dict_list V):
    forall n,
      (contains'' (filter'' f d) n = true) <->
      (exists v, get'' d n = Some v /\ f v = true).
  Proof.
  intros.
  unfold iff.
  split.
  {
    induction d.
    {
      intros.
      simpl in H.
      inversion H.
    }
    destruct a.
    destruct (n_eq_or_neq n n0).
    {
       apply (eq_implies_nat_eq n n0) in H.
       intros.
       exists v.
       unfold get''.
       simpl.
       rewrite H.
       split.
       reflexivity.
       unfold contains'' in H0.
       simpl in H0.
       remember (bool_true_or_false (f v)).
       destruct o.
       apply e.
       rewrite e in H0.
       apply IHd in H0.
       desrtuct 
       red in  H0.
       


  
Admitted.


  (* You (most probably) implemented list-based dictionary in a way
     that doesn't distinguish, say, [(1, 2), (3, 4)] and [(3, 4), (1, 2)] dicts. *)
  (* That is, the results of 'insert', 'contains' and other interface operations
     should be the same for them. *)
  (* Such lists are not-equal, though, 
     since the only list equal to [(1, 2), (3, 4)] is exactly [(1, 2), (3, 4)]. *)
  (* We can formalize the specific notion of equivalence for dictionaries 
     to prove their more complicated properties. *)
  (* Note that this equ ivalence only deals with dict interface 
     and not the particular implementation. *)
  Definition sim_dicts (d1 d2: @nat_dict_list V) :=
    forall n, get'' d1 n = get'' d2 n.

(*...*)

  (* Prove that an insertion makes a preceding removal pointless. 
     To ease the proof, you may want to prove separately that:
     - sim_dicts relation is transitive
     - an insertion of the same key-value pair preserves sim_dicts
     - a double insertion of the same key-value pair
       is similar (in terms of sim_dicts) to a single insertion
     - insertions of separate keys commute
       (that is, their results are related by sim_dicts).
     Also, it can be easier to operate on level of a higher level of 'insert's 
     instead of a lower level of list 'cons'es. 
     To replace 'cons' with 'insert', use 'fold' tactic. 
*)
  Lemma insert_remove_simpl (d: @nat_dict_list V) (n: nat) (v: V):
    sim_dicts (insert'' (remove'' d n) n v) (insert'' d n v).
  Proof.
Admitted.
  
End NatDict'Proofs.   
