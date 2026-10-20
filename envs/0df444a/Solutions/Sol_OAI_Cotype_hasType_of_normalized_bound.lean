-- Prove2me | solution 1 for OAI.Cotype.hasType_of_normalized_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:12:22.994408+00:00
-- url     : https://prove2.me/submissions/9c9e7052-de1c-4c25-8385-7e409b76ab2c

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
theorem h50h_scale {n : ℕ} (c : ℝ) (f : Cube n → X) :
    cubeL2 X (fun ε => c • f ε) = |c| * cubeL2 X f := by
  unfold cubeL2
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_mul (sq_nonneg _)]
  congr 1
  simp only [average, smul_eq_mul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ε _ => ?_
  ring

theorem solution {p D : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (hD : 0 ≤ D)
    (h : ∀ (n : ℕ) (x : Fin n → X), (∑ i, ‖x i‖^p) ≤ 1 →
      cubeL2 X (rademacherSum X x) ≤ D) : HasType X p := by
  refine ⟨hp, hp2, D, hD, fun n x => ?_⟩
  have hp0 : 0 < p := by linarith
  set M := (∑ i, ‖x i‖ ^ p) ^ (1 / p) with hM
  have hsum0 : 0 ≤ ∑ i, ‖x i‖ ^ p := Finset.sum_nonneg fun i _ => by positivity
  rcases hsum0.eq_or_lt with h0 | h0
  · have hx0 : ∀ i, x i = 0 := by
      intro i
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).mp h0.symm i
        (Finset.mem_univ i)
      exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg _) hp0.ne').mp this)
    have : rademacherSum X x = fun _ => 0 := by
      funext ε; simp [rademacherSum, hx0]
    rw [this, hM, ← h0, Real.zero_rpow (by positivity), mul_zero]
    simp [cubeL2, average]
  · have hMpos : 0 < M := Real.rpow_pos_of_pos h0 _
    have hy : ∑ i, ‖M⁻¹ • x i‖ ^ p ≤ 1 := by
      have e : ∀ i, ‖M⁻¹ • x i‖ ^ p = (∑ j, ‖x j‖ ^ p)⁻¹ * ‖x i‖ ^ p := by
        intro i
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hMpos),
          Real.mul_rpow (by positivity) (norm_nonneg _), Real.inv_rpow hMpos.le, hM,
          ← Real.rpow_mul hsum0, one_div_mul_cancel hp0.ne', Real.rpow_one]
      simp only [e, ← Finset.mul_sum, inv_mul_cancel₀ h0.ne', le_refl]
    have hb := h n (fun i => M⁻¹ • x i) hy
    have hr : rademacherSum X (fun i => M⁻¹ • x i) = fun ε => M⁻¹ • rademacherSum X x ε := by
      funext ε; simp only [rademacherSum, Finset.smul_sum, smul_comm M⁻¹]
    rw [hr, h50h_scale, abs_of_pos (inv_pos.mpr hMpos), inv_mul_le_iff₀ hMpos] at hb
    linarith [mul_comm M D]

