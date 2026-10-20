-- Prove2me | solution 2 for OAI.Cotype.fixedCotypeBound_l2Amplification
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:36:17.098415+00:00
-- url     : https://prove2.me/submissions/f0d50dce-fab7-4e4c-86d1-4ee98db64dd2

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CotypeAmplification.lean:L18-L32
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.fixedCotypeBound_l2Amplification. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.Cotype.WalshAmplification ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [NormedSpace ℝ X] [DecidableEq Ω] in
theorem cubeL2_piLp_sq {n : ℕ} (f : Cube n → PiLp 2 (fun _ : Ω => X)) :
    cubeL2 (PiLp 2 (fun _ : Ω => X)) f ^ 2 =
      ∑ a : Ω, cubeL2 X (fun u => f u a) ^ 2 := by
  simp_rw [cubeL2_sq, PiLp.norm_sq_eq_of_L2]
  simp only [average, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.CotypeAmplification ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem fixedCotypeBound_l2Amplification {m : ℕ} {D : ℝ}
    (h : FixedCotypeBound X m D) : FixedCotypeBound (PiLp 2 (fun _ : Ω => X)) m D := by
  refine ⟨h.1, fun x => ?_⟩
  apply (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg h.1 (cubeL2_nonneg _))).mp
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), mul_pow, cubeL2_piLp_sq,
    Finset.mul_sum]
  simp_rw [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro a _
  have ha := (sq_le_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg h.1 (cubeL2_nonneg _))).mpr (h.2 (fun i => x i a))
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)), mul_pow] at ha
  simpa only [rademacherSum_piLp_apply] using ha

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.fixedCotypeBound_l2Amplification := @_root_.OAI.Cotype.fixedCotypeBound_l2Amplification
