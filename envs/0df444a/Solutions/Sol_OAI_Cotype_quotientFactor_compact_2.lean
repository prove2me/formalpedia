-- Prove2me | solution 2 for OAI.Cotype.quotientFactor_compact
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:30:59.052836+00:00
-- url     : https://prove2.me/submissions/140e9ca9-f7a4-43e1-b973-b4d16c15e251

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CompactQuotient.lean:L56-L69
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.quotientFactor_compact. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient

-- ---- from OAI.Analysis.Cotype.CompactQuotient ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem quotient_representative_two (j : H →L[ℝ] X) (g : KernelQuotient j) :
    ∃ z : H, j.ker.mkQL z = g ∧ ‖z‖ ≤ 2 * ‖g‖ := by
  by_cases hg : g = 0
  · exact ⟨0, by simp [hg], by simp [hg]⟩
  · obtain ⟨z,hz,hn⟩ := Submodule.Quotient.norm_mk_lt g (norm_pos_iff.mpr hg)
    exact ⟨z,hz, by linarith⟩

theorem quotientFactor_compact (j : H →L[ℝ] X) (hj : IsCompactOperator j) :
    IsCompactOperator (quotientFactor j) := by
  obtain ⟨K,hK,hjK⟩ := hj.image_closedBall_subset_compact (f := j.toLinearMap) 2
  apply (isCompactOperator_iff_image_closedBall_subset_compact
    (quotientFactor j).toLinearMap (by norm_num : (0:ℝ) < 1)).mpr
  refine ⟨K,hK,?_⟩
  rintro _ ⟨g,hg,rfl⟩
  obtain ⟨z,hz,hn⟩ := quotient_representative_two j g
  apply hjK
  refine ⟨z,?_,?_⟩
  · have hg' : ‖g‖ ≤ 1 := by simpa [Metric.mem_closedBall, dist_zero_right] using hg
    simpa [Metric.mem_closedBall, dist_zero_right] using hn.trans (by linarith : 2*‖g‖ ≤ 2)
  · rw [← hz]
    rfl

variable [CompleteSpace X] (A : ℕ → Submodule ℝ X)

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.quotientFactor_compact := @_root_.OAI.Cotype.quotientFactor_compact
