-- Prove2me | solution 2 for OAI.Cotype.finiteL2Dual_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:38:11.474171+00:00
-- url     : https://prove2.me/submissions/8b0344a5-7d83-4310-b57e-6b7c339d3e59

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FiniteL2DualNorm.lean:L13-L56
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.finiteL2Dual_norm. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_exists_unit_eval_gt

-- ---- from OAI.Analysis.Cotype.FiniteL2Dual ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Ω : Type*} [Fintype Ω]

theorem finiteL2Dual_norm_le (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ ≤ ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ :=
  (finiteL2Dual g).opNorm_le_bound (norm_nonneg _) (finiteL2DualLinear_bound g)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.FiniteL2DualNorm ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
theorem finiteL2Dual_norm (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ = ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ := by
  apply (finiteL2Dual_norm_le g).antisymm
  let R := ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖
  have hR : 0 ≤ R := norm_nonneg _
  have hR2 : R^2 = ∑ i, ‖g i‖^2 := PiLp.norm_sq_eq_of_L2 _ _
  have hsq : R^2 ≤ ‖finiteL2Dual g‖ * R := by
    apply le_of_forall_pos_le_add
    intro ε hε
    let S := ∑ i, ‖g i‖
    have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    let δ := ε / (S+1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    choose x hx he using (fun i => exists_unit_eval_gt (g i) (by linarith : ‖g i‖ - δ < ‖g i‖))
    let z : PiLp 2 (fun _ : Ω => X) := toLp 2 (fun i => ‖g i‖ • x i)
    have hzn : ‖z‖ ≤ R := by
      apply (sq_le_sq₀ (norm_nonneg _) hR).mp
      rw [PiLp.norm_sq_eq_of_L2, hR2]
      apply Finset.sum_le_sum
      intro i _
      have hh : ‖g i‖ * ‖x i‖ ≤ ‖g i‖ := mul_le_of_le_one_right (norm_nonneg _) (hx i)
      simpa only [z, ofLp_toLp, norm_smul, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] using
        (sq_le_sq₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mpr hh
    have hv : finiteL2Dual g z ≤ ‖finiteL2Dual g‖ * R := by
      exact (le_abs_self _).trans ((finiteL2Dual g).le_opNorm z |>.trans
        (mul_le_mul_of_nonneg_left hzn (norm_nonneg _)))
    have hδS : δ * S ≤ ε := by
      have hh : δ * (S+1) = ε := by dsimp [δ]; field_simp
      nlinarith
    calc
      R^2 = ∑ i, ‖g i‖^2 := hR2
      _ ≤ ∑ i, (‖g i‖ * (g i (x i)) + δ * ‖g i‖) :=
        Finset.sum_le_sum (fun i _ => by
          nlinarith [mul_le_mul_of_nonneg_left (show ‖g i‖ ≤ g i (x i) + δ by linarith [he i]) (norm_nonneg (g i))])
      _ = finiteL2Dual g z + δ*S := by
        simp only [finiteL2Dual_apply, z, map_smul, smul_eq_mul, S,
          Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ _ := by linarith
  change R ≤ ‖finiteL2Dual g‖
  by_cases hz : R = 0
  · rw [hz]; exact norm_nonneg _
  have hp : 0 < R := lt_of_le_of_ne hR (Ne.symm hz)
  nlinarith

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.finiteL2Dual_norm := @_root_.OAI.Cotype.finiteL2Dual_norm
