-- Prove2me | solution 1 for OAI.Cotype.fixedCotypeBound_l2Amplification
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:13:33.403378+00:00
-- url     : https://prove2.me/submissions/11b757c1-b2ba-4880-8ab4-c488382b1b45

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

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]


omit [DecidableEq Ω] in
theorem solution {m : ℕ} {D : ℝ}
    (h : FixedCotypeBound X m D) : FixedCotypeBound (PiLp 2 (fun _ : Ω => X)) m D := by
  obtain ⟨hD, hb⟩ := h
  refine ⟨hD, fun x => ?_⟩
  have hsq : ∀ a : Ω, ∑ i, ‖x i a‖ ^ 2 ≤ D ^ 2 * cubeL2 X (rademacherSum X (fun i => x i a)) ^ 2 := by
    intro a
    have := hb (fun i => x i a)
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
    rwa [Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), mul_pow] at h2
  have hrad : ∀ ε a, (rademacherSum (PiLp 2 (fun _ : Ω => X)) x ε) a = rademacherSum X (fun i => x i a) ε := by
    intro ε a
    simp [rademacherSum]
  have hL : ∑ i, ‖x i‖ ^ 2 = ∑ a, ∑ i, ‖x i a‖ ^ 2 := by
    simp only [PiLp.norm_sq_eq_of_L2]; rw [Finset.sum_comm]
  have hR : cubeL2 (PiLp 2 (fun _ : Ω => X)) (rademacherSum _ x) ^ 2 =
      ∑ a, cubeL2 X (rademacherSum X (fun i => x i a)) ^ 2 := by
    simp only [cubeL2_sq, average, smul_eq_mul, PiLp.norm_sq_eq_of_L2, hrad, Finset.mul_sum]
    rw [Finset.sum_comm]
  have key : ∑ i, ‖x i‖ ^ 2 ≤ (D * cubeL2 (PiLp 2 (fun _ : Ω => X)) (rademacherSum _ x)) ^ 2 := by
    rw [hL, mul_pow, hR, Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => hsq a
  calc Real.sqrt (∑ i, ‖x i‖ ^ 2) ≤ Real.sqrt ((D * cubeL2 _ (rademacherSum _ x)) ^ 2) :=
        Real.sqrt_le_sqrt key
    _ = _ := Real.sqrt_sq (mul_nonneg hD (cubeL2_nonneg _))

