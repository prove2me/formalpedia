-- Prove2me | solution 1 for ModernOnlineLearning.Aggregating.restricted_prior_step
-- status  : ACCEPTED   (prove)
-- author  : @suzukasan
-- created : 2026-10-21T04:11:35.059376+00:00
-- url     : https://prove2.me/submissions/d5385c4c-005f-407a-9c5f-bb1a783d3980

import Definitions.Def_ModernOnlineLearning_Aggregating_ExpConcave
import Definitions.Def_ModernOnlineLearning_Aggregating_ShrunkSet
set_option autoImplicit false
open ModernOnlineLearning.Aggregating

theorem solution {d : ℕ} (hd : 0 < d) (T : ℕ) (hT : 0 < T)
    (V : Set (EuclideanSpace ℝ (Fin d))) (hV : Convex ℝ V)
    (u : EuclideanSpace ℝ (Fin d)) (hu : u ∈ V)
    (α : ℝ) (hα : 0 < α)
    (ℓ : ℕ → EuclideanSpace ℝ (Fin d) → ℝ)
    (hℓ : ∀ t ∈ Finset.Icc 1 T, ExpConcaveOn V α (ℓ t)) :
    ∀ x ∈ shrunkSet V u T, ∃ w ∈ V,
      x = (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) • u +
          (1 / ((T : ℝ) / (d : ℝ) + 1)) • w ∧
      (∀ t ∈ Finset.Icc 1 T,
        Real.exp (-α * ℓ t x) ≥
          (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) *
            Real.exp (-α * ℓ t u) +
          (1 / ((T : ℝ) / (d : ℝ) + 1)) * Real.exp (-α * ℓ t w) ∧
        (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) *
            Real.exp (-α * ℓ t u) +
          (1 / ((T : ℝ) / (d : ℝ) + 1)) * Real.exp (-α * ℓ t w) ≥
          (((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) *
            Real.exp (-α * ℓ t u)) ∧
      Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t x) ≥
        ((((T : ℝ) / (d : ℝ)) / ((T : ℝ) / (d : ℝ) + 1)) ^ T) *
        Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) ∧
      Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t x) ≥
        Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) / Real.exp (d : ℝ) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hTR : (0 : ℝ) < T := by exact_mod_cast hT
  let r : ℝ := ((T : ℝ) / d) / ((T : ℝ) / d + 1)
  let s : ℝ := 1 / ((T : ℝ) / d + 1)
  have hden : 0 < (T : ℝ) / d + 1 := by positivity
  have hr : 0 < r := div_pos (div_pos hTR hdR) hden
  have hs : 0 < s := div_pos zero_lt_one hden
  have hrs : r + s = 1 := by dsimp [r, s]; field_simp
  intro x hx
  obtain ⟨w, hw, hwx⟩ := hx
  have hxrep : x = r • u + s • w := hwx.symm
  have hround : ∀ t ∈ Finset.Icc 1 T,
      r * Real.exp (-α * ℓ t u) + s * Real.exp (-α * ℓ t w) ≤ Real.exp (-α * ℓ t x) ∧
      r * Real.exp (-α * ℓ t u) ≤ r * Real.exp (-α * ℓ t u) + s * Real.exp (-α * ℓ t w) := by
    intro t ht
    constructor
    · rw [hxrep]
      exact (hℓ t ht).2 hu hw hr.le hs.le hrs
    · linarith [mul_pos hs (Real.exp_pos (-α * ℓ t w))]
  have hpoint : ∀ t ∈ Finset.Icc 1 T,
      Real.log r + -α * ℓ t u ≤ -α * ℓ t x := by
    intro t ht
    have h := Real.log_le_log (mul_pos hr (Real.exp_pos _)) ((hround t ht).2.trans (hround t ht).1)
    simpa only [Real.log_mul hr.ne' (Real.exp_ne_zero _), Real.log_exp] using h
  have hsum : (T : ℝ) * Real.log r + -α * ∑ t ∈ Finset.Icc 1 T, ℓ t u ≤
      -α * ∑ t ∈ Finset.Icc 1 T, ℓ t x := by
    have h := Finset.sum_le_sum hpoint
    simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul] using h
  have hexp := Real.exp_le_exp.mpr hsum
  rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hr] at hexp
  have hlog : -(d : ℝ) ≤ (T : ℝ) * Real.log r := by
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hr) hTR.le
    have heq : (T : ℝ) * (1 - r⁻¹) = -(d : ℝ) := by
      dsimp [r]
      field_simp
      ring
    rwa [heq] at h
  refine ⟨w, hw, hxrep, hround, hexp, ?_⟩
  have hlast := Real.exp_le_exp.mpr (add_le_add_right hlog (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u))
  rw [Real.exp_add, Real.exp_neg, Real.exp_add, Real.exp_nat_mul, Real.exp_log hr] at hlast
  change Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) / Real.exp (d : ℝ) ≤ _
  calc
    _ = (Real.exp (d : ℝ))⁻¹ * Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) := by ring
    _ ≤ r ^ T * Real.exp (-α * ∑ t ∈ Finset.Icc 1 T, ℓ t u) := by simpa [mul_comm] using hlast
    _ ≤ _ := hexp


