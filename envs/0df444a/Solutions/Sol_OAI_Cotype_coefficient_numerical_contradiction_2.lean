-- Prove2me | solution 2 for OAI.Cotype.coefficient_numerical_contradiction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-20T00:00:33.983272+00:00
-- url     : https://prove2.me/submissions/78b4e7dd-a7d5-458e-ad65-9675f44b286e

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/CoefficientArithmetic.lean:L10-L36
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.coefficient_numerical_contradiction. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.CoefficientArithmetic ----
namespace OAI

namespace Cotype

theorem coefficient_numerical_contradiction {A B d : ℝ} (hd : 4 ≤ d)
    (hA : 80 * d * (d+1)^2 ≤ A) (hB : 80 * d * (d+1)^2 ≤ B)
    (hupper : A * B / 2 ≤ 4 * d * (d+1) * (A+B+10*d*(d+1)^2)) : False := by
  set t := d * (d+1) with htdef
  set u := d * (d+1)^2 with hudef
  have ht : 0 < t := by dsimp [t]; positivity
  have hu : 0 < u := by dsimp [u]; positivity
  have hA' : 80 * u ≤ A := by nlinarith [hA]
  have hB' : 80 * u ≤ B := by nlinarith [hB]
  have hAn : 0 ≤ A := by linarith
  have hBn : 0 ≤ B := by linarith
  have hC : 0 < A+B := by linarith
  have hut : 5*t ≤ u := by
    have hh := mul_nonneg (show 0 ≤ d*(d+1) by positivity) (show 0 ≤ d-4 by linarith)
    dsimp [t, u]
    nlinarith [hh]
  have hp : 40*u*(A+B) ≤ A*B := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hA') hBn,
      mul_nonneg (sub_nonneg.mpr hB') hAn]
  have hs : 160*u ≤ A+B := by linarith
  have hlow : (17/4:ℝ)*t*(A+B) < 20*u*(A+B) := by
    nlinarith [mul_pos ht hC, mul_nonneg (sub_nonneg.mpr hut) hC.le]
  have hhigh : 4*t*(A+B+10*u) ≤ (17/4:ℝ)*t*(A+B) := by
    nlinarith [mul_nonneg ht.le (sub_nonneg.mpr hs)]
  have hupper' : A*B/2 ≤ 4*t*(A+B+10*u) := by
    convert hupper using 1; dsimp [t, u]; ring
  linarith

end Cotype

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.coefficient_numerical_contradiction := @_root_.OAI.Cotype.coefficient_numerical_contradiction
