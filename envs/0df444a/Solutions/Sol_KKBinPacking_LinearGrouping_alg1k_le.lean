-- Prove2me | solution 1 for KKBinPacking.LinearGrouping.alg1k_le
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T10:22:39.23892+00:00
-- url     : https://prove2.me/submissions/209bc96d-410c-4cb6-b281-9b18465662a3

import Definitions.Def_KKBinPacking_LinearGrouping_Algorithm1
import Definitions.Def_KKBinPacking_LinearGrouping_Instance
import Mathlib.Data.Finset.Max
import Mathlib.Order.Lattice.Nat
open KKBinPacking.LinearGrouping

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


private theorem size_le_opt (I : Multiset ℝ) (hI : IsInstance I) : SIZE I ≤ (OPT I : ℝ) := by
  obtain ⟨P,hP,hcard⟩:=opt_attained I hI
  simpa only [hcard] using size_le_card I P hP

private theorem sum_filter_le (I : Multiset ℝ) (hI : IsInstance I) (p : ℝ → Prop) [DecidablePred p] :
    (I.filter p).sum ≤ I.sum := by
  induction I using Multiset.induction_on with
  | empty => simp
  | @cons a I ih =>
    have ha:=(hI a (by simp)).1
    have hh:=ih (fun b hb => hI b (by simp [hb]))
    by_cases hp : p a
    · simpa [hp] using add_le_add_left hh a
    · simpa [hp] using hh.trans (by linarith : I.sum ≤ a+I.sum)

private theorem card_mul_le_sum (I : Multiset ℝ) (a : ℝ) (ha : ∀ b ∈ I,a ≤ b) :
    (I.card : ℝ)*a ≤ I.sum := by
  induction I using Multiset.induction_on with
  | empty => simp
  | @cons b I ih =>
    have hb:=ha b (by simp)
    have hh:=ih (fun c hc => ha c (by simp [hc]))
    simp only [Multiset.card_cons,Multiset.sum_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

theorem solution (ε : ℝ) (hε : 0 < ε) (I : Multiset ℝ) (hI : IsInstance I) :
    (alg1k ε I : ℝ) ≤ 2 * ε * (OPT I : ℝ) + 1 := by
  have hsum : ((alg1J ε I).card : ℝ)*(ε/2) ≤ (OPT I : ℝ) := by
    apply (card_mul_le_sum (alg1J ε I) (ε/2) ?_).trans
    · exact (sum_filter_le I hI _).trans (size_le_opt I hI)
    · intro a ha
      have hh:=(Multiset.mem_filter.mp ha).2
      exact (le_max_right _ _).trans hh.le
  have hk : (alg1k ε I : ℝ) < ((alg1J ε I).card : ℝ)*ε^2+1 := by
    apply Nat.ceil_lt_add_one
    positivity
  have hh:=mul_le_mul_of_nonneg_left hsum (show 0 ≤ 2*ε by positivity)
  nlinarith
