-- Prove2me | solution 1 for KKBinPacking.GeometricGrouping.opt_le_two_size_add_one
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T15:05:45.497759+00:00
-- url     : https://prove2.me/submissions/b2060619-28e6-4011-af6a-d8026d7d5540

import Definitions.Def_KKBinPacking_GeometricGrouping_Instance
import Mathlib.Data.Finset.Max
import Mathlib.Order.Lattice.Nat
open KKBinPacking.GeometricGrouping

private theorem packing_exists (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ P, IsPacking I P := by
  refine ⟨I.map (fun a => ({a} : Multiset ℝ)),?_,?_⟩
  · induction I using Multiset.induction_on with
    | empty => simp
    | cons a I ih => simpa [Multiset.map_cons,Multiset.join_cons] using congrArg (fun J => a ::ₘ J) (ih (fun b hb => hI b (by simp [hb])))
  · intro b hb
    obtain ⟨a,ha,rfl⟩:=Multiset.mem_map.mp hb
    simpa using (hI a ha).2.le

private theorem opt_attained (I : Multiset ℝ) (hI : IsInstance I) :
    ∃ P, IsPacking I P ∧ P.card=OPT I := by
  obtain ⟨P,hP⟩:=packing_exists I hI
  have hn : Set.Nonempty {B : ℕ | ∃ P : Multiset (Multiset ℝ),IsPacking I P ∧ P.card=B} := ⟨P.card,P,hP,rfl⟩
  exact Nat.sInf_mem hn

private theorem opt_le_card (I : Multiset ℝ) (P : Multiset (Multiset ℝ))
    (hP : IsPacking I P) : OPT I ≤ P.card :=
  Nat.sInf_le ⟨P,hP,rfl⟩

private theorem bin_nonneg (I : Multiset ℝ) (hI : IsInstance I)
    (P : Multiset (Multiset ℝ)) (hP : IsPacking I P) (b : Multiset ℝ) (hb : b ∈ P) :
    0 ≤ b.sum := by
  apply Multiset.sum_nonneg
  intro a ha
  exact (hI a (by rw [← hP.1];exact Multiset.mem_join.mpr ⟨b,hb,ha⟩)).1.le

private theorem optimal_bins_separate (I : Multiset ℝ)
    (P : Multiset (Multiset ℝ)) (hP : IsPacking I P) (hcard : P.card=OPT I)
    (b c : Multiset ℝ) (hb : b ∈ P) (hc : c ∈ P.erase b) : 1 < b.sum+c.sum := by
  classical
  by_contra hn
  have hbc : b.sum+c.sum ≤ 1 := le_of_not_gt hn
  let Q:=(b+c) ::ₘ ((P.erase b).erase c)
  have he : P=b ::ₘ c ::ₘ ((P.erase b).erase c) := by
    rw [Multiset.cons_erase hc,Multiset.cons_erase hb]
  have hQ : IsPacking I Q := by
    constructor
    · have hh:=hP.1
      rw [he] at hh
      simpa [Q,Multiset.join_cons,add_assoc] using hh
    · intro a ha
      rcases Multiset.mem_cons.mp ha with rfl|ha
      · simpa using hbc
      · exact hP.2 a (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase ha))
  have ho:=opt_le_card I Q hQ
  rw [← hcard,he] at ho
  simp only [Q,Multiset.card_cons] at ho
  omega

private theorem size_le_card (I : Multiset ℝ) (P : Multiset (Multiset ℝ))
    (hP : IsPacking I P) : SIZE I ≤ (P.card : ℝ) := by
  have hh (Q : Multiset (Multiset ℝ)) : (∀ b ∈ Q,b.sum ≤ 1) → (Q.map Multiset.sum).sum ≤ (Q.card : ℝ) := by
    induction Q using Multiset.induction_on with
    | empty => simp
    | @cons b Q ih =>
      intro h
      have hb:=h b (by simp)
      have hQ:=ih (fun a ha => h a (by simp [ha]))
      simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,Nat.cast_add,Nat.cast_one]
      linarith
  rw [SIZE,← hP.1,Multiset.sum_join]
  exact hh P hP.2

theorem solution (I : Multiset ℝ) (hI : IsInstance I) :
    (OPT I : ℝ) ≤ 2 * SIZE I + 1 := by
  classical
  obtain ⟨P,hP,hcard⟩:=opt_attained I hI
  by_cases hzero : P=0
  · rw [← hcard,hzero]
    have hi : I=0 := by simpa [hzero] using hP.1.symm
    simp [hi,SIZE]
  obtain ⟨b,hb,hmin⟩:=Multiset.exists_min_image Multiset.sum hzero
  have hrest (c : Multiset ℝ) (hc : c ∈ P.erase b) : (1/2:ℝ) ≤ c.sum := by
    have hh:=optimal_bins_separate I P hP hcard b c hb hc
    have hm:=hmin c (Multiset.mem_of_mem_erase hc)
    linarith
  have hsum (Q : Multiset (Multiset ℝ)) : (∀ c ∈ Q,(1/2:ℝ) ≤ c.sum) →
      (Q.card : ℝ)/2 ≤ (Q.map Multiset.sum).sum := by
    induction Q using Multiset.induction_on with
    | empty => simp
    | @cons c Q ih =>
      intro h
      have hc:=h c (by simp)
      have hQ:=ih (fun a ha => h a (by simp [ha]))
      simp only [Multiset.map_cons,Multiset.sum_cons,Multiset.card_cons,Nat.cast_add,Nat.cast_one]
      linarith
  have hh:=hsum (P.erase b) hrest
  have hb0:=bin_nonneg I hI P hP b hb
  have he : P=b ::ₘ P.erase b := (Multiset.cons_erase hb).symm
  have hi : SIZE I=b.sum+((P.erase b).map Multiset.sum).sum := by
    calc
      SIZE I = P.join.sum := by rw [hP.1];rfl
      _ = (b ::ₘ P.erase b).join.sum := congrArg (fun Q : Multiset (Multiset ℝ) => Q.join.sum) he
      _ = _ := by rw [Multiset.join_cons,Multiset.sum_add,Multiset.sum_join]
  rw [← hcard,he,Multiset.card_cons,Nat.cast_add,Nat.cast_one,hi]
  linarith
