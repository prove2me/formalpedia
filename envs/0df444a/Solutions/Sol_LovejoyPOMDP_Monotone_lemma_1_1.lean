-- Prove2me | solution 1 for LovejoyPOMDP.Monotone.lemma_1_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T04:13:28.671512+00:00
-- url     : https://prove2.me/submissions/42ab72b6-d219-407e-8d43-9f6988a3c167

import Mathlib
import Definitions.Def_LovejoyPOMDP_Monotone_Orders

set_option autoImplicit false
open LovejoyPOMDP.Monotone

theorem abel_aux {X : Type*} [LinearOrder X] (f : X → ℝ) (hf : Monotone f) (s : Finset X) :
    ∀ d : X → ℝ, ∑ i ∈ s, d i = 0 → (∀ q, 0 ≤ ∑ i ∈ s.filter (fun i => q ≤ i), d i) →
      0 ≤ ∑ i ∈ s, d i * f i := by
  induction s using Finset.induction_on_min with
  | empty => intro d _ _; simp
  | insert a s ha ih =>
    intro d hsum htail
    have hna : a ∉ s := fun h => lt_irrefl a (ha a h)
    rcases s.eq_empty_or_nonempty with rfl | hne
    · simp at hsum ⊢
      simp [hsum]
    · set b := s.min' hne with hb
      have hbs : b ∈ s := Finset.min'_mem s hne
      have hab : a < b := ha b hbs
      have hbs' : ∀ i ∈ s, b ≤ i := fun i hi => Finset.min'_le s i hi
      rw [Finset.sum_insert hna] at hsum
      let d' : X → ℝ := fun i => d i + if i = b then d a else 0
      have hd'sum : ∑ i ∈ s, d' i = 0 := by
        simp only [d', Finset.sum_add_distrib, Finset.sum_ite_eq', if_pos hbs]
        linarith
      have hd'tail : ∀ q, 0 ≤ ∑ i ∈ s.filter (fun i => q ≤ i), d' i := by
        intro q
        by_cases hq : q ≤ b
        · have : s.filter (fun i => q ≤ i) = s := by
            apply Finset.filter_true_of_mem
            intro i hi; exact le_trans hq (hbs' i hi)
          rw [this, hd'sum]
        · push_neg at hq
          have h1 : ∑ i ∈ s.filter (fun i => q ≤ i), d' i = ∑ i ∈ s.filter (fun i => q ≤ i), d i := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [Finset.mem_filter] at hi
            have : i ≠ b := by
              intro hib; rw [hib] at hi; exact absurd hi.2 (not_le.mpr hq)
            simp [d', this]
          have h2 := htail q
          rw [Finset.filter_insert, if_neg (not_le.mpr (lt_trans hab hq)), ] at h2
          rw [h1]; exact h2
      have hih := ih d' hd'sum hd'tail
      have hda : d a ≤ 0 := by
        have h3 := htail b
        rw [Finset.filter_insert, if_neg (not_le.mpr hab)] at h3
        have : s.filter (fun i => b ≤ i) = s := Finset.filter_true_of_mem hbs'
        rw [this] at h3
        linarith
      have hfab : f a ≤ f b := hf hab.le
      have hexp : ∑ i ∈ s, d' i * f i = ∑ i ∈ s, d i * f i + d a * f b := by
        simp only [d', add_mul, Finset.sum_add_distrib]
        congr 1
        rw [Finset.sum_congr rfl (fun i _ => by rw [ite_mul, zero_mul])]
        rw [Finset.sum_ite_eq' s b, if_pos hbs]
      rw [Finset.sum_insert hna]
      nlinarith [mul_nonneg (neg_nonneg.mpr hda) (sub_nonneg.mpr hfab)]

theorem solution {X : Type*} [Fintype X] [LinearOrder X] {π π' : X → ℝ}
    (hπ : π ∈ stdSimplex ℝ X) (hπ' : π' ∈ stdSimplex ℝ X) :
    StochGE π π' ↔ ∀ f : X → ℝ, Monotone f → ∑ i, π' i * f i ≤ ∑ i, π i * f i := by
  constructor
  · intro h f hf
    have := abel_aux f hf Finset.univ (fun i => π i - π' i)
      (by rw [Finset.sum_sub_distrib, hπ.2, hπ'.2]; ring)
      (by
        intro q
        rw [Finset.sum_sub_distrib]
        linarith [h q])
    simp only [sub_mul, Finset.sum_sub_distrib] at this
    linarith
  · intro h q
    have := h (fun i => if q ≤ i then (1:ℝ) else 0) (by
      intro i j hij
      by_cases hi : q ≤ i
      · have : q ≤ j := le_trans hi hij
        simp [hi, this]
      · simp only [hi, if_false]
        split_ifs <;> norm_num)
    simpa [Finset.sum_filter] using this
