-- Prove2me | solution 1 for OAI.Cotype.tuple_dual_lq_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:10:52.029057+00:00
-- url     : https://prove2.me/submissions/9bb601b6-f74d-4362-a72c-7ba4f2709891

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem h50t_eval (φ : X →L[ℝ] ℝ) {a : ℝ} (ha : a < ‖φ‖) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ a < φ x := by
  rcases lt_or_ge a 0 with h | h
  · exact ⟨0, by simp, by simpa using h⟩
  obtain ⟨x, hx1, hx2⟩ := φ.exists_lt_apply_of_lt_opNorm (r := a) ha
  rcases le_or_gt 0 (φ x) with h0 | h0
  · exact ⟨x, hx1.le, by rwa [Real.norm_eq_abs, abs_of_nonneg h0] at hx2⟩
  · refine ⟨-x, by rw [norm_neg]; exact hx1.le, ?_⟩
    rw [map_neg]
    rwa [Real.norm_eq_abs, abs_of_neg h0] at hx2

theorem solution {n : ℕ} (φ : Fin n → (X →L[ℝ] ℝ))
    {p q C : ℝ} (hp : 1 < p) (hq : 1 < q) (hpq : (q-1)*p = q) (hC : 0 ≤ C)
    (h : ∀ x : Fin n → X, |∑ i, φ i (x i)| ≤ C*(∑ i, ‖x i‖^p)^(1/p)) :
    (∑ i, ‖φ i‖^q)^(1/q) ≤ C := by
  set S := ∑ i, ‖φ i‖ ^ q with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by linarith
  have hexp : (1 / q) = 1 - 1 / p := by field_simp; linarith
  have key : ∀ ε > 0, S ≤ C * S ^ (1 / p) + ε * ∑ i, ‖φ i‖ ^ (q - 1) := by
    intro ε hε
    choose u hu1 hu2 using fun i => h50t_eval (φ i) (sub_lt_self (‖φ i‖) hε)
    let x : Fin n → X := fun i => (‖φ i‖ ^ (q - 1)) • u i
    have hxn : ∀ i, ‖x i‖ ^ p ≤ ‖φ i‖ ^ q := by
      intro i
      have h1 : ‖x i‖ ≤ ‖φ i‖ ^ (q - 1) := by
        simp only [x, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : (0:ℝ) ≤ ‖φ i‖ ^ (q - 1))]
        simpa using mul_le_mul_of_nonneg_left (hu1 i) (by positivity : (0:ℝ) ≤ ‖φ i‖ ^ (q - 1))
      calc ‖x i‖ ^ p ≤ (‖φ i‖ ^ (q - 1)) ^ p := Real.rpow_le_rpow (norm_nonneg _) h1 hp0.le
        _ = ‖φ i‖ ^ q := by rw [← Real.rpow_mul (norm_nonneg _), hpq]
    have hsum : ∑ i, ‖x i‖ ^ p ≤ S := Finset.sum_le_sum fun i _ => hxn i
    have hlow : S - ε * ∑ i, ‖φ i‖ ^ (q - 1) ≤ ∑ i, φ i (x i) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      simp only [x, map_smul, smul_eq_mul]
      have hpow : ‖φ i‖ ^ q = ‖φ i‖ ^ (q - 1) * ‖φ i‖ := by
        rcases (norm_nonneg (φ i)).eq_or_lt with h0 | h0
        · rw [← h0, Real.zero_rpow hq0.ne', Real.zero_rpow (by linarith), zero_mul]
        · rw [← Real.rpow_add_one h0.ne']; congr 1; ring
      rw [hpow]
      have := mul_le_mul_of_nonneg_left (hu2 i).le (by positivity : (0:ℝ) ≤ ‖φ i‖ ^ (q - 1))
      linarith [show ‖φ i‖ ^ (q - 1) * ‖φ i‖ - ε * ‖φ i‖ ^ (q - 1) =
        ‖φ i‖ ^ (q - 1) * (‖φ i‖ - ε) by ring]
    have hup : ∑ i, φ i (x i) ≤ C * S ^ (1 / p) := by
      calc ∑ i, φ i (x i) ≤ |∑ i, φ i (x i)| := le_abs_self _
        _ ≤ C * (∑ i, ‖x i‖ ^ p) ^ (1 / p) := h x
        _ ≤ C * S ^ (1 / p) := mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow (Finset.sum_nonneg fun i _ => by positivity) hsum (by positivity)) hC
    linarith
  have hS : S ≤ C * S ^ (1 / p) := by
    refine le_of_forall_pos_le_add fun δ hδ => ?_
    set T := ∑ i, ‖φ i‖ ^ (q - 1)
    have hT : 0 ≤ T := Finset.sum_nonneg fun i _ => by positivity
    have := key (δ / (T + 1)) (by positivity)
    have : δ / (T + 1) * T ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  rcases hS0.eq_or_lt with h0 | h0
  · rw [← h0, Real.zero_rpow (by positivity)]; exact hC
  · rw [hexp, Real.rpow_sub h0, Real.rpow_one, div_le_iff₀ (Real.rpow_pos_of_pos h0 _)]
    exact hS

