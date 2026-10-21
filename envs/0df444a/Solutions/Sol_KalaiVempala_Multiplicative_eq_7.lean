-- Prove2me | solution 1 for KalaiVempala.Multiplicative.eq_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T05:55:13.856495+00:00
-- url     : https://prove2.me/submissions/c4c29c83-dfd9-40e5-a39d-f6aa5b21b67a

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

set_option autoImplicit false
open MeasureTheory OracleRO.ApproxFPL KalaiVempala.Multiplicative

theorem int_lap {n : ℕ} (ε : ℝ) (hε : 0 < ε) (F : (Fin n → ℝ) → ℝ) :
    ∫ x, F x ∂(laplaceLaw n ε) =
      ∫ x, ((ε / 2) ^ n * Real.exp (-(ε * ∑ i, |x i|))) * F x := by
  unfold laplaceLaw
  have hmeas : Measurable (fun x : Fin n → ℝ =>
      ENNReal.ofReal ((ε / 2) ^ n * Real.exp (-(ε * ∑ i, |x i|)))) := by
    apply ENNReal.measurable_ofReal.comp
    fun_prop
  rw [integral_withDensity_eq_integral_toReal_smul hmeas
    (Filter.Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have h0 : 0 ≤ (ε / 2) ^ n * Real.exp (-(ε * ∑ i, |x i|)) := by positivity
  simp [ENNReal.toReal_ofReal h0]

theorem solution {n : ℕ} (M : (Fin n → ℝ) → (Fin n → ℝ)) (hMmeas : Measurable M)
    (s : ℕ → Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) (t : ℕ) (ht : 1 ≤ t) :
    ∫ x, M (prefixSum s (t - 1) + x) ⬝ᵥ s t ∂(laplaceLaw n ε) =
      ∫ y, (M (prefixSum s t + y) ⬝ᵥ s t) *
          Real.exp (-(ε * (∑ i, |y i + s t i| - ∑ i, |y i|))) ∂(laplaceLaw n ε) := by
  rw [int_lap ε hε, int_lap ε hε]
  have hP : prefixSum s t = prefixSum s (t - 1) + s t := by
    obtain ⟨u, rfl⟩ : ∃ u, t = u + 1 := ⟨t - 1, by omega⟩
    simp only [prefixSum, Nat.add_sub_cancel]
    rw [Finset.sum_Icc_succ_top (by omega)]
  set φ : (Fin n → ℝ) → ℝ := fun x => (ε / 2) ^ n * Real.exp (-(ε * ∑ i, |x i|)) with hφ
  have hshift := integral_add_right_eq_self (μ := volume)
    (fun x : Fin n → ℝ => φ x * (M (prefixSum s (t - 1) + x) ⬝ᵥ s t)) (s t)
  rw [← hshift]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [hφ]
  have e1 : (ε / 2) ^ n * Real.exp (-(ε * ∑ i, |(y + s t) i|)) =
      (ε / 2) ^ n * Real.exp (-(ε * ∑ i, |y i|)) *
        Real.exp (-(ε * (∑ i, |y i + s t i| - ∑ i, |y i|))) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    simp only [Pi.add_apply]
    ring
  have e2 : prefixSum s (t - 1) + (y + s t) = prefixSum s t + y := by
    rw [hP]; abel
  rw [e1, e2]
  ring
