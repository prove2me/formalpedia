-- Prove2me | solution 1 for Kyprianou.Ch02.aeBVUniformGridAbsoluteSumsBoundedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:15:07.67581+00:00
-- url     : https://prove2.me/submissions/e516d853-5cf9-4313-b864-d3fc5852868a

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → ℝ)
    (hBV : ∀ᵐ ω ∂P, LocallyBoundedVariationOn
      (fun t : ℝ≥0 => X t ω) Set.univ) :
    ∀ᵐ ω ∂P, ∃ B : ℝ, ∀ n : ℕ,
      (∑ i : Fin (n + 1),
          |X (((i.val + 1 : ℕ) : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω -
           X ((i.val : ℝ≥0) * (((n : ℝ≥0) + 1)⁻¹)) ω|) ≤ B := by
  filter_upwards [hBV] with ω hω
  let V := eVariationOn (fun t : ℝ≥0 => X t ω) (Set.univ ∩ Icc 0 1)
  have hV : V ≠ ⊤ := hω 0 1 (mem_univ _) (mem_univ _)
  refine ⟨V.toReal, ?_⟩
  intro n
  let h : ℝ≥0 := ((n : ℝ≥0) + 1)⁻¹
  let q : ℕ → ℝ≥0 := fun i => (min i (n + 1) : ℝ≥0) * h
  have hq : Monotone q := by
    intro i k hik
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_min_right (n + 1) hik) (by positivity)
  have hqmem (i : ℕ) : q i ∈ (Set.univ ∩ Icc (0 : ℝ≥0) 1) := by
    refine ⟨mem_univ _, ⟨by positivity, ?_⟩⟩
    calc
      q i ≤ ((n : ℝ≥0) + 1) * h :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast min_le_right i (n + 1)) (by positivity)
      _ = 1 := mul_inv_cancel₀ (by positivity)
  have hs := eVariationOn.sum_le (f := fun t => X t ω)
    (n := n + 1) hq hqmem
  apply (ENNReal.ofReal_le_iff_le_toReal hV).mp
  let f (i : ℕ) : ℝ := |X (((i + 1 : ℕ) : ℝ≥0) * h) ω -
    X ((i : ℝ≥0) * h) ω|
  change ENNReal.ofReal (∑ i : Fin (n + 1), f i.val) ≤ V
  rw [Fin.sum_univ_eq_sum_range f, ENNReal.ofReal_sum_of_nonneg (fun i _ => show 0 ≤ f i from abs_nonneg _)]
  refine le_trans ?_ hs
  apply le_of_eq
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i + 1 ≤ n + 1 := Nat.succ_le_of_lt (Finset.mem_range.mp hi)
  have hi'' : i ≤ n + 1 := by omega
  have h1 : (i : ℝ≥0) + 1 ≤ (n : ℝ≥0) + 1 := by exact_mod_cast hi'
  have h2 : (i : ℝ≥0) ≤ (n : ℝ≥0) + 1 := by exact_mod_cast hi''
  simp [f, q, h, min_eq_left hi', min_eq_left hi'', min_eq_left h1,
    min_eq_left h2, edist_dist, Real.dist_eq]
