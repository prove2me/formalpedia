-- Prove2me | solution 2 for OAI.Cotype.grouped_vector_generating
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:58:20.200491+00:00
-- url     : https://prove2.me/submissions/6948e2f3-6f47-454d-a4c1-64005c554842

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ProjectionDerivatives.lean:L23-L42
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.grouped_vector_generating. The node keeps its source
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
import Theorems.Thm_OAI_Cotype_fourier_inversion

-- ---- from OAI.Analysis.Cotype.BiasedFourier ----
namespace OAI

noncomputable section
open scoped BigOperators
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem biasedExpectation_character (t : ι → ℝ) (p : ι → Bool) :
    biasedExpectation (character p) t = ∏ i, if p i then t i else 1 := by
  unfold biasedExpectation biasWeight character
  simp only [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    ((1 + t i * sign b) / 2) * (if p i then sign b else 1))]
  apply Finset.prod_congr rfl
  intro i _
  cases p i <;> simp only [Fintype.sum_bool, sign_false, sign_true, Bool.false_eq_true,
    ite_false, ite_true] <;> ring

theorem biasedExpectation_fourier (f : (ι → Bool) → ℝ) (t : ι → ℝ) :
    biasedExpectation f t = ∑ p, fourier f p * ∏ i, if p i then t i else 1 := by
  calc
    biasedExpectation f t = ∑ ε, biasWeight t ε *
        ∑ p, fourier f p * character p ε := by simp only [fourier_inversion, biasedExpectation]
    _ = ∑ p, fourier f p * biasedExpectation (character p) t := by
      simp only [biasedExpectation, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro ε _
      ring
    _ = _ := by simp_rw [biasedExpectation_character]

theorem biasedExpectation_common_mean (f : (ι → Bool) → ℝ) (t : ℝ) :
    biasedExpectation f (fun _ => t) =
      ∑ p, fourier f p * t ^ (Finset.univ.filter (fun i => p i = true)).card := by
  rw [biasedExpectation_fourier]
  simp [← Finset.prod_filter]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ProjectionDerivatives ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial
namespace Cotype
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable {m : ℕ}

theorem grouped_vector_generating (g : Cube m → ℝ) (x : ℝ) :
    (∑ l ∈ Finset.range (m+1), levelFourier g l * x^l) =
      biasedExpectation g (fun _ => x) := by
  have hf (l : ℕ) : (Finset.univ : Finset (Fin m)).powersetCard l =
      Finset.univ.filter (fun t : Finset (Fin m) => t.card = l) := by
    ext t
    simp [Finset.mem_powersetCard]
  simp only [levelFourier, hf, Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  have he (t : Finset (Fin m)) :
      (∑ l ∈ Finset.range (m+1), (if t.card = l then fourier g (setIndex t) else 0) * x^l) =
        fourier g (setIndex t) * x^t.card := by
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp [show t.card < m+1 by have h := Finset.card_le_univ t; simp at h; omega]
  simp_rw [he]
  rw [biasedExpectation_common_mean]
  apply Fintype.sum_equiv setIndexEquiv
  intro t
  simp [setIndexEquiv, setIndex]

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open Polynomial


theorem solution : type_of% @_root_.OAI.Cotype.grouped_vector_generating := @_root_.OAI.Cotype.grouped_vector_generating
