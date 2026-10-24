-- Prove2me | solution 1 for HiringLP.ProbeTopK.dr_properties
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T18:53:53.61249+00:00
-- url     : https://prove2.me/submissions/f2880f87-e65e-4e90-bd92-1df8dc51b85c

import Mathlib
import Definitions.Def_HiringLP_ProbeTopK_Model
import Theorems.Thm_HiringLP_ProbeTopK_lemma_2

set_option autoImplicit false
open Finset HiringLP.ProbeTopK

namespace PTKDR

section Bern
variable {ι : Type*} [DecidableEq ι]

def WW (q : ι → ℝ) (S A : Finset ι) : ℝ := ∏ i ∈ S, if i ∈ A then q i else 1 - q i

theorem WW_insert (q : ι → ℝ) (a : ι) (S : Finset ι) (ha : a ∉ S) (Φ : Finset ι → ℝ) :
    ∑ A ∈ (insert a S).powerset, WW q (insert a S) A * Φ A =
      (1 - q a) * ∑ A ∈ S.powerset, WW q S A * Φ A +
        q a * ∑ A ∈ S.powerset, WW q S A * Φ (insert a A) := by
  rw [sum_powerset_insert ha, mul_sum, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro A hA
    have haA : a ∉ A := fun h => ha (mem_powerset.1 hA h)
    unfold WW
    rw [prod_insert ha, if_neg haA]; ring
  · apply sum_congr rfl
    intro A _
    unfold WW
    rw [prod_insert ha, if_pos (mem_insert_self a A)]
    have : ∏ i ∈ S, (if i ∈ insert a A then q i else 1 - q i) =
        ∏ i ∈ S, (if i ∈ A then q i else 1 - q i) := by
      apply prod_congr rfl
      intro i hi
      have hia : i ≠ a := fun h => ha (h ▸ hi)
      simp [mem_insert, hia]
    rw [this]; ring

theorem WW_one (q : ι → ℝ) (S : Finset ι) : ∑ A ∈ S.powerset, WW q S A = 1 := by
  induction S using Finset.induction_on with
  | empty => simp [WW]
  | insert a S ha ih =>
    have := WW_insert q a S ha (fun _ => 1)
    simp only [mul_one] at this
    rw [this, ih]; ring

theorem WW_lin (q : ι → ℝ) (f : ι → ℝ) (S : Finset ι) :
    ∑ A ∈ S.powerset, WW q S A * ∑ i ∈ A, f i = ∑ i ∈ S, f i * q i := by
  induction S using Finset.induction_on with
  | empty => simp [WW]
  | insert a S ha ih =>
    rw [WW_insert q a S ha, sum_insert ha]
    have e : ∑ A ∈ S.powerset, WW q S A * ∑ i ∈ insert a A, f i =
        ∑ A ∈ S.powerset, (WW q S A * f a + WW q S A * ∑ i ∈ A, f i) := by
      apply sum_congr rfl
      intro A hA
      have haA : a ∉ A := fun h => ha (mem_powerset.1 hA h)
      rw [sum_insert haA]; ring
    rw [e, sum_add_distrib, ← sum_mul, WW_one, ih]; ring

end Bern

theorem DR_eq_indep {n : ℕ} (y : Fin n → ℝ) (hy : ∀ i, 0 ≤ y i ∧ y i ≤ 1)
    (hF : (fracSet y).card ≠ 2) (S : Finset (Fin n)) : DR y S = WW y univ S := by
  unfold DR WW
  rw [if_neg hF]
  have hzero : ∀ i, i ∉ onesSet y ∪ fracSet y → y i = 0 := by
    intro i hi
    simp only [onesSet, fracSet, mem_union, mem_filter, mem_univ, true_and, not_or,
      not_and_or, not_lt] at hi
    rcases hi with ⟨h1, h2 | h2⟩
    · linarith [(hy i).1]
    · exact absurd (le_antisymm (hy i).2 h2) h1
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    refine prod_subset (subset_univ _) ?_
    intro i _ hi
    by_cases hone : i ∈ onesSet y
    · have : y i = 1 := by simpa [onesSet] using hone
      rw [if_pos (h1 hone), this]
    · have hnot : i ∉ onesSet y ∪ fracSet y := by simp [hone, hi]
      have hiS : i ∉ S := fun h => hnot (h2 h)
      rw [if_neg hiS, hzero i hnot]; ring
  · symm
    rw [not_and_or] at h
    rcases h with h | h
    · obtain ⟨i, hi1, hi2⟩ := not_subset.1 h
      have : y i = 1 := by simpa [onesSet] using hi1
      exact prod_eq_zero (mem_univ i) (by rw [if_neg hi2, this]; ring)
    · obtain ⟨i, hi1, hi2⟩ := not_subset.1 h
      exact prod_eq_zero (mem_univ i) (by rw [if_pos hi1, hzero i hi2])

end PTKDR

open PTKDR in
theorem solution {n J : ℕ} (I : Instance n J) (hI : I.Valid)
    (x : Fin n → Fin J → ℝ) (y : Fin n → ℝ)
    (hext : (x, y) ∈ Set.extremePoints ℝ (feasibleSet I)) :
    (∀ S, 0 ≤ DR y S) ∧ (∑ S, DR y S = 1) ∧
      (∀ i, ∑ S, DR y S * (if i ∈ S then 1 else 0) = y i) ∧
      ∀ S, DR y S ≠ 0 → S.card ≤ I.T := by
  have hf : LPFeasible I x y := hext.1
  have hy := hf.2.2.2.2
  have hL2 := lemma_2 I hI x y hext
  set O := onesSet y with hO
  have hfrb : ∀ i ∈ fracSet y, 0 < y i ∧ y i < 1 := fun i hi => by simpa [fracSet] using hi
  have hnf : ∀ i, i ∉ fracSet y → y i = 0 ∨ y i = 1 := by
    intro i hi
    simp only [fracSet, mem_filter, mem_univ, true_and, not_and_or, not_lt] at hi
    rcases hi with h | h
    · left; linarith [(hy i).1]
    · right; linarith [(hy i).2]
  have hdisj : Disjoint O (fracSet y) := by
    rw [disjoint_left]; intro i hi hi'
    have := (hfrb i hi').2
    simp only [hO, onesSet, mem_filter, mem_univ, true_and] at hi
    linarith
  have hsumy : ∑ i, y i = (O.card : ℝ) + ∑ i ∈ fracSet y, y i := by
    have hdecomp : ∀ i, y i = (if i ∈ O then 1 else 0) + (if i ∈ fracSet y then y i else 0) := by
      intro i
      by_cases hif : i ∈ fracSet y
      · have hno : i ∉ O := fun h => disjoint_left.1 hdisj h hif
        simp [hif, hno]
      · rcases hnf i hif with h | h
        · have hno : i ∉ O := by simp [hO, onesSet, h]
          simp [hif, hno, h]
        · have hyes : i ∈ O := by simp [hO, onesSet, h]
          simp [hif, hyes, h]
    rw [sum_congr rfl (fun i _ => hdecomp i), sum_add_distrib, sum_boole, ← sum_filter]
    have e : (univ.filter fun i => i ∈ O) = O := by ext; simp
    have e2 : (univ.filter fun i => i ∈ fracSet y) = fracSet y := by ext; simp
    rw [e, e2]
  have hsupp : ∀ S, DR y S ≠ 0 → O ⊆ S ∧ S ⊆ O ∪ fracSet y := by
    intro S hS
    by_contra hc
    exact hS (by unfold DR; rw [if_neg hc])
  have hnonneg : ∀ S, 0 ≤ DR y S := by
    intro S
    unfold DR
    split_ifs
    · exact sum_nonneg (fun i _ => (hy i).1)
    · exact le_rfl
    · exact prod_nonneg (fun i _ => by split_ifs <;> linarith [hy i])
    · exact le_rfl
  refine ⟨hnonneg, ?_⟩
  by_cases hF : (fracSet y).card = 2
  · obtain ⟨a, b, hab, hfr⟩ := card_eq_two.1 hF
    have ha : a ∈ fracSet y := by rw [hfr]; simp
    have hb : b ∈ fracSet y := by rw [hfr]; simp
    have hsum1 : y a + y b = 1 := by
      have := hL2.2 hF; rw [hfr, sum_pair hab] at this; exact this
    have haO : a ∉ O := fun h => disjoint_left.1 hdisj h ha
    have hbO : b ∉ O := fun h => disjoint_left.1 hdisj h hb
    have hne : insert a O ≠ insert b O := by
      intro h
      have : a ∈ insert b O := h ▸ mem_insert_self a O
      rcases mem_insert.1 this with h' | h'
      · exact hab h'
      · exact haO h'
    have hval : ∀ c ∈ fracSet y, c ∉ O → DR y (insert c O) = y c := by
      intro c hc hcO
      unfold DR
      have hsd : insert c O \ onesSet y = {c} := by
        ext i; simp only [mem_sdiff, mem_insert, mem_singleton, ← hO]
        constructor
        · rintro ⟨h | h, h'⟩
          · exact h
          · exact absurd h h'
        · rintro rfl; exact ⟨Or.inl rfl, hcO⟩
      rw [if_pos ⟨subset_insert _ _, insert_subset (mem_union_right _ hc) subset_union_left⟩,
        if_pos hF, hsd, card_singleton, if_pos rfl, sum_singleton]
    have hshape : ∀ S, DR y S ≠ 0 → S = insert a O ∨ S = insert b O := by
      intro S hS
      obtain ⟨hc1, hc2⟩ := hsupp S hS
      have hcard : (S \ onesSet y).card = 1 := by
        by_contra hc
        exact hS (by unfold DR; rw [if_pos ⟨hc1, hc2⟩, if_pos hF, if_neg hc])
      obtain ⟨c, hc⟩ := card_eq_one.1 hcard
      have hcS : c ∈ S \ onesSet y := by rw [hc]; exact mem_singleton_self c
      have hcfr : c ∈ fracSet y := by
        rcases mem_union.1 (hc2 (mem_sdiff.1 hcS).1) with h | h
        · exact absurd h (mem_sdiff.1 hcS).2
        · exact h
      have hSeq : S = insert c O := by
        ext i
        simp only [mem_insert]
        constructor
        · intro hi
          by_cases hiO : i ∈ onesSet y
          · exact Or.inr hiO
          · left
            have : i ∈ S \ onesSet y := mem_sdiff.2 ⟨hi, hiO⟩
            rw [hc] at this; exact mem_singleton.1 this
        · rintro (rfl | hi)
          · exact (mem_sdiff.1 hcS).1
          · exact hc1 hi
      rw [hfr] at hcfr
      rcases mem_insert.1 hcfr with h | h
      · left; rw [hSeq, h]
      · right; rw [hSeq, mem_singleton.1 h]
    have hexp : ∀ g : Finset (Fin n) → ℝ,
        ∑ S, DR y S * g S = y a * g (insert a O) + y b * g (insert b O) := by
      intro g
      rw [sum_eq_add_of_mem (insert a O) (insert b O) (mem_univ _) (mem_univ _) hne, hval a ha haO,
        hval b hb hbO]
      intro S _ hS
      by_contra h0
      rcases hshape S (left_ne_zero_of_mul h0) with h | h
      · exact hS.1 h
      · exact hS.2 h
    refine ⟨?_, ?_, ?_⟩
    · have := hexp (fun _ => 1); simp only [mul_one] at this; rw [this, hsum1]
    · intro i
      rw [hexp]
      by_cases hiO : i ∈ O
      · have : y i = 1 := by simpa [hO, onesSet] using hiO
        simp only [mem_insert, hiO, or_true, if_true, mul_one]; rw [this, hsum1]
      · by_cases hia : i = a
        · subst hia
          have : i ∉ insert b O := by simp [hab, haO]
          simp [this]
        · by_cases hib : i = b
          · subst hib
            have : i ∉ insert a O := by simp [Ne.symm hab, hbO]
            simp [this]
          · have hif : i ∉ fracSet y := by rw [hfr]; simp [hia, hib]
            have hy0 : y i = 0 := by
              rcases hnf i hif with h | h
              · exact h
              · exact absurd (by simp [hO, onesSet, h]) hiO
            simp [hia, hib, hiO, hy0]
    · intro S hS
      have hT := hf.2.1
      rw [hsumy, hfr, sum_pair hab, hsum1] at hT
      have hc : S.card = O.card + 1 := by
        rcases hshape S hS with h | h
        · rw [h, card_insert_of_notMem haO]
        · rw [h, card_insert_of_notMem hbO]
      have : ((S.card : ℕ) : ℝ) ≤ I.T := by rw [hc]; push_cast; linarith
      exact_mod_cast this
  · have hDR : ∀ S, DR y S = WW y univ S := DR_eq_indep y hy hF
    have hpow : ∀ g : Finset (Fin n) → ℝ, ∑ S, g S = ∑ S ∈ (univ : Finset (Fin n)).powerset, g S := by
      intro g; rw [powerset_univ]
    refine ⟨?_, ?_, ?_⟩
    · simp only [hDR]; rw [hpow (fun S => WW y univ S), WW_one]
    · intro i
      simp only [hDR]
      rw [hpow (fun S => WW y univ S * if i ∈ S then 1 else 0)]
      have := WW_lin y (fun l => if l = i then 1 else 0) univ
      simp only [sum_ite_eq', mem_univ, if_true, ite_mul, one_mul, zero_mul] at this
      rw [← this]
    · intro S hS
      obtain ⟨hc1, hc2⟩ := hsupp S hS
      have hcS : S.card ≤ O.card + (fracSet y).card :=
        (card_le_card hc2).trans (card_union_le _ _)
      have hT := hf.2.1
      rw [hsumy] at hT
      have hle2 := hL2.1
      have hcases : (fracSet y).card = 0 ∨ (fracSet y).card = 1 := by omega
      rcases hcases with h0 | h1
      · rw [card_eq_zero.1 h0, sum_empty, add_zero] at hT
        have : ((S.card : ℕ) : ℝ) ≤ I.T := by
          have : (S.card : ℝ) ≤ O.card := by exact_mod_cast (by omega : S.card ≤ O.card)
          linarith
        exact_mod_cast this
      · obtain ⟨a, ha⟩ := card_eq_one.1 h1
        have hya := hfrb a (by rw [ha]; simp)
        rw [ha, sum_singleton] at hT
        have hlt : (O.card : ℝ) < I.T := by linarith
        have hlt' : O.card < I.T := by exact_mod_cast hlt
        omega
