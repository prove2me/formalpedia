-- Prove2me | solution 1 for GreshamLaw.optimal_payment_iff_exchange
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T19:44:05.351222+00:00
-- url     : https://prove2.me/submissions/327175bd-488c-4c9a-9121-fe238714ef3c

import Mathlib
import Definitions.Def_GreshamLaw_Model
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open GreshamLaw
private theorem gresham_retained {ι : Type*} [DecidableEq ι]
    (coin : ι → Coin) (s R : Finset ι) (hR : R ⊆ s) :
    totalMelt coin (s \ R) + totalMelt coin R = totalMelt coin s := by
  unfold totalMelt
  have h := Finset.sum_sdiff hR (f := fun i => (coin i).melt)
  linarith
private theorem gresham_payment_card {ι : Type*} [DecidableEq ι]
    (coin : ι → Coin) (s P Q : Finset ι) (d : ℝ)
    (heq : EqualLegalTender coin s) (hpos : ∀ i ∈ s, 0 < (coin i).face)
    (hP : IsLegalPayment coin s P d) (hQ : IsLegalPayment coin s Q d) :
    P.card = Q.card := by
  classical
  rcases hP with ⟨hPs, hPd⟩
  rcases hQ with ⟨hQs, hQd⟩
  by_cases hs : s = ∅
  · have hp : P = ∅ := Finset.subset_empty.mp (by simpa [hs] using hPs)
    have hq : Q = ∅ := Finset.subset_empty.mp (by simpa [hs] using hQs)
    simp [hp, hq]
  · obtain ⟨z, hz⟩ : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs
    have htotal (R : Finset ι) (hRs : R ⊆ s) :
        totalFace coin R = (R.card : ℝ) * (coin z).face := by
      unfold totalFace
      calc
        (∑ i ∈ R, (coin i).face) = ∑ i ∈ R, (coin z).face := by
          apply Finset.sum_congr rfl
          intro i hi
          exact heq i (hRs hi) z hz
        _ = (R.card : ℝ) * (coin z).face := by simp
    have hPval := htotal P hPs
    have hQval := htotal Q hQs
    have hzero : ((P.card : ℝ) - (Q.card : ℝ)) * (coin z).face = 0 := by
      nlinarith [hPval, hQval, hPd, hQd]
    have hneq : (coin z).face ≠ 0 := ne_of_gt (hpos z hz)
    have heqcard : (P.card : ℝ) = (Q.card : ℝ) := by
      rcases mul_eq_zero.mp hzero with hzero' | hbad
      · linarith
      · exact False.elim (hneq hbad)
    exact_mod_cast heqcard
private theorem gresham_pairwise_sum {ι : Type*} [DecidableEq ι]
    (A B : Finset ι) (f : ι → ℝ) (hc : A.card = B.card)
    (hle : ∀ i ∈ A, ∀ j ∈ B, f i ≤ f j) :
    (∑ i ∈ A, f i) ≤ ∑ j ∈ B, f j := by
  classical
  induction A using Finset.induction_on generalizing B with
  | empty =>
      have hB : B = ∅ := Finset.card_eq_zero.mp (by simpa using hc.symm)
      simp [hB]
  | @insert a A ha ih =>
      have hBcard : 0 < B.card := by
        have ha' : 0 < (insert a A).card := by simp [ha]
        omega
      obtain ⟨b, hb⟩ := Finset.card_pos.mp hBcard
      have hc' : A.card = (B.erase b).card := by
        have hA := Finset.card_insert_of_notMem ha
        have hB := Finset.card_erase_of_mem hb
        omega
      have hle' : ∀ i ∈ A, ∀ j ∈ B.erase b, f i ≤ f j := by
        intro i hi j hj
        exact hle i (Finset.mem_insert_of_mem hi) j (Finset.mem_of_mem_erase hj)
      have hsum := ih (B.erase b) hc' hle'
      have hab : f a ≤ f b := hle a (Finset.mem_insert_self a A) b hb
      have hright := Finset.sum_erase_add (s := B) (f := f) hb
      rw [Finset.sum_insert ha]
      linarith
theorem solution {ι : Type*} [DecidableEq ι] (coin : ι → Coin)
    (s P : Finset ι) (d : ℝ)
    (hlegal : EqualLegalTender coin s) (hpos : ∀ i ∈ s, 0 < (coin i).face) :
    IsOptimalPayment coin s P d ↔
      IsLegalPayment coin s P d ∧ ∀ i ∈ P, ∀ j ∈ s \ P,
        (coin i).melt ≤ (coin j).melt := by
  classical
  constructor
  · rintro ⟨hLP, hopt⟩
    refine ⟨hLP, ?_⟩
    intro i hi j hj
    have hjS : j ∈ s := (Finset.mem_sdiff.mp hj).1
    have hjNot : j ∉ P := (Finset.mem_sdiff.mp hj).2
    have hiS : i ∈ s := hLP.1 hi
    let Q : Finset ι := insert j (P.erase i)
    have hjEr : j ∉ P.erase i := by simp [hjNot]
    have hQs : Q ⊆ s := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | he
      · exact hjS
      · exact hLP.1 (Finset.mem_of_mem_erase he)
    have hswap (f : ι → ℝ) :
        (∑ x ∈ Q, f x) = (∑ x ∈ P, f x) + f j - f i := by
      have he := Finset.sum_erase_add (s := P) (f := f) hi
      calc
        (∑ x ∈ Q, f x) = f j + ∑ x ∈ P.erase i, f x := by
          simp [Q, hjEr]
        _ = (∑ x ∈ P, f x) + f j - f i := by linarith
    have hface : (coin j).face = (coin i).face := hlegal j hjS i hiS
    have hQface : totalFace coin Q = totalFace coin P := by
      unfold totalFace
      rw [hswap]
      linarith
    have hQL : IsLegalPayment coin s Q d := ⟨hQs, hQface.trans hLP.2⟩
    have hQP : totalMelt coin P ≤ totalMelt coin Q := by
      have hh := hopt Q hQL
      have hretP := gresham_retained coin s P hLP.1
      have hretQ := gresham_retained coin s Q hQs
      linarith
    have hmelts : totalMelt coin Q =
        totalMelt coin P + (coin j).melt - (coin i).melt := by
      unfold totalMelt
      exact hswap (fun x => (coin x).melt)
    linarith
  · rintro ⟨hLP, horder⟩
    refine ⟨hLP, ?_⟩
    intro Q hLQ
    have hc : P.card = Q.card :=
      gresham_payment_card coin s P Q d hlegal hpos hLP hLQ
    have hdiffcard : (P \ Q).card = (Q \ P).card :=
      Finset.card_sdiff_eq_card_sdiff_iff.mpr hc
    have hbound : (∑ i ∈ P \ Q, (coin i).melt) ≤
        (∑ j ∈ Q \ P, (coin j).melt) := by
      apply gresham_pairwise_sum (P \ Q) (Q \ P)
        (fun i => (coin i).melt) hdiffcard
      intro i hi j hj
      apply horder i (Finset.mem_sdiff.mp hi).1 j
      exact Finset.mem_sdiff.mpr ⟨hLQ.1 (Finset.mem_sdiff.mp hj).1,
        (Finset.mem_sdiff.mp hj).2⟩
    let K : Finset ι := P ∩ Q
    have hKP : K ⊆ P := Finset.inter_subset_left
    have hKQ : K ⊆ Q := Finset.inter_subset_right
    have hdiffP : P \ K = P \ Q := by ext x; simp [K]
    have hdiffQ : Q \ K = Q \ P := by ext x; simp [K]
    have hsumP : (∑ i ∈ P \ Q, (coin i).melt) +
        (∑ i ∈ K, (coin i).melt) = totalMelt coin P := by
      have hh := Finset.sum_sdiff hKP (f := fun i => (coin i).melt)
      rw [hdiffP] at hh
      unfold totalMelt
      linarith
    have hsumQ : (∑ i ∈ Q \ P, (coin i).melt) +
        (∑ i ∈ K, (coin i).melt) = totalMelt coin Q := by
      have hh := Finset.sum_sdiff hKQ (f := fun i => (coin i).melt)
      rw [hdiffQ] at hh
      unfold totalMelt
      linarith
    have hretP := gresham_retained coin s P hLP.1
    have hretQ := gresham_retained coin s Q hLQ.1
    linarith
