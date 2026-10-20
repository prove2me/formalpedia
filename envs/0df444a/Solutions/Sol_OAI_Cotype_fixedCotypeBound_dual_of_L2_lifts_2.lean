-- Prove2me | solution 2 for OAI.Cotype.fixedCotypeBound_dual_of_L2_lifts
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:29:04.002131+00:00
-- url     : https://prove2.me/submissions/2dd30f43-24e4-4781-8994-aff8e93b36f7

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/DualCotypeFromLifts.lean:L11-L29
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.fixedCotypeBound_dual_of_L2_lifts. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_average_norm_mul_le
import Theorems.Thm_OAI_Cotype_finiteL2Dual_norm

-- ---- from OAI.Analysis.Cotype.WalshDuality ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem dualPairing_bound {n : ℕ} (f : Cube n → X) (g : Cube n → (X →L[ℝ] ℝ)) :
    |dualPairing f g| ≤ cubeL2 X f * cubeL2 (X →L[ℝ] ℝ) g := by
  calc
    _ ≤ average (fun u => |g u (f u)|) := by
      simpa only [dualPairing, Real.norm_eq_abs] using norm_average_le (fun u => g u (f u))
    _ ≤ average (fun u => ‖f u‖ * ‖g u‖) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum (fun u _ => by
        simpa only [Real.norm_eq_abs, mul_comm] using (g u).le_opNorm (f u))
    _ ≤ _ := average_norm_mul_le f g

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.DualCotypeFromLifts ----
namespace OAI

noncomputable section
open scoped BigOperators
open WithLp
namespace Cotype
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem fixedCotypeBound_dual_of_L2_lifts {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z : Fin m → X, ∃ H : Cube m → X,
      (∀ i, moment X H i = z i) ∧ cubeL2 X H ≤ C * Real.sqrt (∑ i, ‖z i‖^2)) :
    FixedCotypeBound (X →L[ℝ] ℝ) m C := by
  refine ⟨hC, fun θ => ?_⟩
  have hb : ‖finiteL2Dual θ‖ ≤ C * cubeL2 (X →L[ℝ] ℝ) (rademacherSum (X →L[ℝ] ℝ) θ) := by
    apply (finiteL2Dual θ).opNorm_le_bound (mul_nonneg hC (cubeL2_nonneg _))
    intro z
    obtain ⟨H,hm,hn⟩ := h (fun i => z i)
    have he : finiteL2Dual θ z = dualPairing H (rademacherSum (X →L[ℝ] ℝ) θ) := by
      simp only [finiteL2Dual_apply, ← hm, dualPairing, rademacherSum, moment,
        average, map_smul, map_sum, sum_apply, smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    rw [he, Real.norm_eq_abs]
    have hn' : cubeL2 X H ≤ C * ‖z‖ := by simpa only [PiLp.norm_eq_of_L2] using hn
    calc
      _ ≤ cubeL2 X H * cubeL2 (X →L[ℝ] ℝ) (rademacherSum (X →L[ℝ] ℝ) θ) := dualPairing_bound _ _
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hn' (cubeL2_nonneg (rademacherSum (X →L[ℝ] ℝ) θ))]
  simpa only [finiteL2Dual_norm, PiLp.norm_eq_of_L2, ofLp_toLp] using hb

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open WithLp


theorem solution : type_of% @_root_.OAI.Cotype.fixedCotypeBound_dual_of_L2_lifts := @_root_.OAI.Cotype.fixedCotypeBound_dual_of_L2_lifts
