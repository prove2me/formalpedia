-- Prove2me | solution 2 for OAI.Cotype.finiteSupDual_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:32:01.788726+00:00
-- url     : https://prove2.me/submissions/b6c044e0-5200-483e-9227-34c795d670a9

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FiniteSupDual.lean:L48-L68
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.finiteSupDual_norm. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_exists_unit_eval_gt

-- ---- from OAI.Analysis.Cotype.FiniteSupDual ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω]

theorem finiteSupDual_norm (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteSupDual g‖ = ∑ a, ‖g a‖ := by
  apply le_antisymm
  · exact (finiteSupDual g).opNorm_le_bound (Finset.sum_nonneg (fun a _ => norm_nonneg _))
      (finiteSupDualLinear_bound g)
  · apply le_of_forall_pos_le_add
    intro ε hε
    let δ := ε / (Fintype.card Ω + 1)
    have hδ : 0 < δ := div_pos hε (by positivity)
    choose x hx he using (fun a => exists_unit_eval_gt (g a) (by linarith : ‖g a‖ - δ < ‖g a‖))
    have hxn : ‖x‖ ≤ 1 := (pi_norm_le_iff_of_nonneg (by positivity)).mpr hx
    have hv : (finiteSupDual g) x ≤ ‖finiteSupDual g‖ :=
      (le_abs_self _).trans ((finiteSupDual g).le_opNorm x |>.trans
        ((mul_le_mul_of_nonneg_left hxn (norm_nonneg _)).trans_eq (mul_one _)))
    have hδcard : (Fintype.card Ω : ℝ) * δ ≤ ε := by
      have hh : (Fintype.card Ω + 1) * δ = ε := by dsimp [δ]; field_simp
      nlinarith
    calc
      ∑ a, ‖g a‖ ≤ ∑ a, (g a (x a) + δ) := Finset.sum_le_sum (fun a _ => by linarith [he a])
      _ = finiteSupDual g x + (Fintype.card Ω : ℝ) * δ := by simp [Finset.sum_add_distrib]
      _ ≤ _ := by linarith

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.finiteSupDual_norm := @_root_.OAI.Cotype.finiteSupDual_norm
