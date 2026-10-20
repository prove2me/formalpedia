-- Prove2me | solution 2 for OAI.Cotype.compactMap_walsh_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:34:14.555352+00:00
-- url     : https://prove2.me/submissions/0200ee6b-41ff-480b-b323-b3313bd95c75

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/WalshMainEstimates.lean:L39-L58
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.compactMap_walsh_bound. The node keeps its source
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
import Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
import Definitions.Def_OAI_Analysis_Cotype_PatternPairing
import Definitions.Def_OAI_Analysis_Cotype_TaggedFrames
import Definitions.Def_OAI_Analysis_Cotype_CoefficientTarget
import Definitions.Def_OAI_Analysis_Cotype_DampedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_GroupedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ProjectionCoefficients
import Definitions.Def_OAI_Analysis_Cotype_PatternNormalization
import Definitions.Def_OAI_Analysis_Cotype_PatternProjections
import Definitions.Def_OAI_Analysis_Cotype_DeletedTail
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevBounds
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevTruncation
import Definitions.Def_OAI_Analysis_Cotype_BivariateSplit
import Definitions.Def_OAI_Analysis_Cotype_ProjectionDerivatives
import Definitions.Def_OAI_Analysis_Cotype_MixedDerivative
import Definitions.Def_OAI_Analysis_Cotype_CoefficientCompactness
import Definitions.Def_OAI_Analysis_Cotype_GrowthScalarData
import Definitions.Def_OAI_Analysis_Cotype_TaggedCoefficient
import Definitions.Def_OAI_Analysis_Cotype_RankWalsh
import Definitions.Def_OAI_Analysis_Cotype_UniformDecay
import Definitions.Def_OAI_Analysis_Cotype_CompactDomain
import Theorems.Thm_OAI_Cotype_walshNorm_lipschitz

-- ---- from OAI.Analysis.Cotype.Approximation ----
namespace OAI

noncomputable section
namespace Cotype
variable {X G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem compactMap_approximation (hAP : ApproximationProperty X)
    (J : G →L[ℝ] X) (hJ : IsCompactOperator J) {δ : ℝ} (hδ : 0 < δ) :
    ∃ S : X →L[ℝ] X,
      FiniteDimensional ℝ (LinearMap.range S.toLinearMap) ∧ ‖S.comp J - J‖ < δ := by
  have hK : IsCompact (closure (J '' Metric.closedBall 0 1)) :=
    hJ.isCompact_closure_image_closedBall (f := J.toLinearMap) 1
  obtain ⟨S, hS, herr⟩ := hAP _ hK (δ / 2) (by positivity)
  refine ⟨S, hS, lt_of_le_of_lt ?_ (by linarith : δ / 2 < δ)⟩
  apply ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity)
  intro z hz
  have hzK : J z ∈ closure (J '' Metric.closedBall 0 1) :=
    subset_closure ⟨z, by simp [Metric.mem_closedBall, dist_zero_right, hz], rfl⟩
  simpa using (herr (J z) hzK).le

theorem compactMap_finiteRank_approximation (hAP : ApproximationProperty X)
    (J : G →L[ℝ] X) (hJ : IsCompactOperator J) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T : G →L[ℝ] X,
      FiniteDimensional ℝ (LinearMap.range T.toLinearMap) ∧ ‖T - J‖ < δ := by
  obtain ⟨S, hS, herr⟩ := compactMap_approximation hAP J hJ hδ
  let := hS
  refine ⟨S.comp J, ?_, herr⟩
  apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range S.toLinearMap)
  exact LinearMap.range_comp_le_range _ _

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.WalshMainEstimates ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

theorem compactMap_walsh_bound (hAP : ApproximationProperty X)
    (J : G →L[ℝ] X) (hJ : IsCompactOperator J) (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hfin : ∀ T : G →L[ℝ] X, FiniteDimensional ℝ (LinearMap.range T.toLinearMap) →
      walshNorm n T ≤ ρ * ‖T‖) :
    walshNorm n J ≤ ρ * ‖J‖ := by
  by_contra hn
  have hp : 0 < walshNorm n J - ρ * ‖J‖ := sub_pos.mpr (lt_of_not_ge hn)
  let δ := (walshNorm n J - ρ * ‖J‖) / (2 * (ρ+1))
  have hδ : 0 < δ := div_pos hp (by positivity)
  obtain ⟨T, hT, herr⟩ := compactMap_finiteRank_approximation hAP J hJ hδ
  have hw := (abs_le.mp (walshNorm_lipschitz n J T)).2
  rw [norm_sub_rev] at hw
  have hnT : ‖T‖ ≤ ‖J‖ + ‖T-J‖ := by
    simpa only [sub_add_cancel] using (norm_add_le (T-J) J).trans_eq (add_comm _ _)
  have hTbound := hfin T hT
  have he : δ * (2 * (ρ+1)) = walshNorm n J - ρ * ‖J‖ := by
    dsimp [δ]
    field_simp
  nlinarith [mul_le_mul_of_nonneg_left hnT hρ,
    mul_lt_mul_of_pos_left herr (show 0 < ρ+1 by positivity)]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators


theorem solution : type_of% @_root_.OAI.Cotype.compactMap_walsh_bound := @_root_.OAI.Cotype.compactMap_walsh_bound
