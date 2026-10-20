-- Prove2me | solution 2 for OAI.Cotype.rowProjection_oddPart
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:46:05.732224+00:00
-- url     : https://prove2.me/submissions/0ea30b05-58a3-4d25-b57c-598e0a3db39f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/PatternProjections.lean:L13-L27
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.rowProjection_oddPart. The node keeps its source
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

-- ---- from OAI.Analysis.Cotype.Fourier ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem average_negate {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : (ι → Bool) → E) : average (fun ε => f (negateCube ε)) = average f := by
  unfold average
  congr 1
  exact Fintype.sum_equiv negateEquiv _ _ (fun _ => rfl)

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.PatternNormalization ----
namespace OAI

noncomputable section

open scoped BigOperators
namespace Cotype
variable {α : Type*} [Fintype α]

theorem average_mul_right (f : α → ℝ) (c : ℝ) :
    average (fun x => f x * c) = average f * c := average_smul_const f c

theorem average_sub_real (f g : α → ℝ) :
    average (fun x => f x - g x) = average f - average g := by
  simp [average, Finset.sum_sub_distrib, mul_sub]

theorem average_div_real (f : α → ℝ) (c : ℝ) :
    average (fun x => f x / c) = average f / c := by
  simp only [div_eq_mul_inv, average_mul_right]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
theorem xorCube_negate_left (a b : ι → Bool) :
    xorCube (negateCube a) b = negateCube (xorCube a b) := by
  funext i; simp [xorCube, negateCube]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.PatternProjections ----
namespace OAI

noncomputable section

namespace Cotype
variable {m : ℕ}

theorem rowProjection_oddPart (F : SignMatrix m → ℝ) (i : Fin m) (S : SignMatrix m) :
    rowProjection (oddPart F) i S = rowProjection F i S := by
  have hn : average (fun σ : Cube m => sign (σ i) * F (negateCube (xorCube (rowCube σ) S))) =
      -rowProjection F i S := by
    rw [← average_negate (fun σ : Cube m => sign (σ i) * F (negateCube (xorCube (rowCube σ) S)))]
    have he (σ : Cube m) : negateCube (xorCube (rowCube (negateCube σ)) S) =
        xorCube (rowCube σ) S := by
      change negateCube (xorCube (negateCube (rowCube σ)) S) = _
      rw [xorCube_negate_left, negateCube_negateCube]
    simp only [he, negateCube, sign_not, neg_mul]
    simp [rowProjection, average]
  simp only [rowProjection, oddPart, ← mul_div_assoc, mul_sub, average_div_real, average_sub_real]
  rw [hn]
  unfold rowProjection
  ring

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype


theorem solution : type_of% @_root_.OAI.Cotype.rowProjection_oddPart := @_root_.OAI.Cotype.rowProjection_oddPart
