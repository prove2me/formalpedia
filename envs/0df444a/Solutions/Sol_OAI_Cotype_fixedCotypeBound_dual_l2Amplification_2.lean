-- Prove2me | solution 2 for OAI.Cotype.fixedCotypeBound_dual_l2Amplification
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T22:40:10.223754+00:00
-- url     : https://prove2.me/submissions/c08ef5c9-1b46-45c9-8b45-b4fe5d204d6c

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/FiniteL2DualNorm.lean:L63-L80
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.fixedCotypeBound_dual_l2Amplification. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_finiteL2Dual_norm
import Theorems.Thm_OAI_Cotype_fixedCotypeBound_l2Amplification

-- ---- from OAI.Analysis.Cotype.PrimalMomentLifts ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

theorem tupleDual_eq (ψ : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) :
    ψ = finiteL2Dual (tupleDualCoordinates ψ) := by
  ext z
  have hs : (∑ i : Ω, PiLp.single 2 i (z i)) = z := by ext j; simp
  simp only [finiteL2Dual_apply, tupleDualCoordinates, ContinuousLinearMap.comp_apply, singleL2_apply]
  rw [← map_sum, hs]

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

theorem tupleDualCoordinates_norm (ψ : PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) :
    ‖(toLp 2 (tupleDualCoordinates ψ) : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ = ‖ψ‖ := by
  rw [← finiteL2Dual_norm]
  exact congrArg norm (tupleDual_eq ψ).symm

theorem fixedCotypeBound_dual_l2Amplification {m : ℕ} {D : ℝ}
    (hD : FixedCotypeBound (X →L[ℝ] ℝ) m D) :
    FixedCotypeBound (PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) m D := by
  have h := fixedCotypeBound_l2Amplification (Ω := Ω) hD
  refine ⟨hD.1, fun x => ?_⟩
  let y : Fin m → PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)) :=
    fun i => toLp 2 (tupleDualCoordinates (x i))
  have hy : ∀ i, ‖y i‖ = ‖x i‖ := fun i => tupleDualCoordinates_norm (x i)
  have hr (u : Cube m) : rademacherSum (PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ))) y u =
      toLp 2 (tupleDualCoordinates (rademacherSum (PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) x u)) := by
    ext a z
    simp [rademacherSum, tupleDualCoordinates, y]
  have hnorm : cubeL2 (PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))
      (rademacherSum (PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ))) y) =
      cubeL2 (PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ)
        (rademacherSum (PiLp 2 (fun _ : Ω => X) →L[ℝ] ℝ) x) := by
    simp only [cubeL2, hr, tupleDualCoordinates_norm]
  simpa only [hy, hnorm] using h.2 y

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.fixedCotypeBound_dual_l2Amplification := @_root_.OAI.Cotype.fixedCotypeBound_dual_l2Amplification
