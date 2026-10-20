-- Prove2me | solution 1 for OAI.Cotype.grouped_vector_generating
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:29:46.644198+00:00
-- url     : https://prove2.me/submissions/c245bc56-8378-43e8-bd7e-804797022ad0

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

open OAI OAI.Cotype
open scoped BigOperators
open Polynomial
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {m : ℕ}


theorem solution (g : Cube m → ℝ) (x : ℝ) :
    (∑ l ∈ Finset.range (m+1), levelFourier g l * x^l) =
      biasedExpectation g (fun _ => x) := by
  classical
  have hN : (Fintype.card (Cube m) : ℝ) = 2 ^ m := by simp [Cube]
  have hchar : ∀ (t : Finset (Fin m)) (ε : Cube m),
      character (setIndex t) ε = ∏ i ∈ t, sign (ε i) := by
    intro t ε
    unfold character setIndex
    rw [← Finset.prod_filter]
    congr 1; ext i; simp
  have hw : ∀ ε : Cube m, biasWeight (fun _ => x) ε =
      ∑ t ∈ (Finset.univ : Finset (Fin m)).powerset, x ^ t.card * (1/2 : ℝ) ^ m * character (setIndex t) ε := by
    intro ε
    unfold biasWeight
    have : ∀ i, (1 + x * sign (ε i)) / 2 = x * sign (ε i) / 2 + 1 / 2 := fun i => by ring
    simp only [this]
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hchar, Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
      Finset.prod_const, Finset.card_univ_diff, Fintype.card_fin]
    have ht : t.card ≤ m := by simpa using t.card_le_univ
    have h2 : (1/2 : ℝ) ^ m = (1/2) ^ t.card * (1/2) ^ (m - t.card) := by
      rw [← pow_add, Nat.add_sub_cancel' ht]
    rw [h2]; field_simp
    rw [mul_assoc, ← mul_pow]; norm_num
  unfold biasedExpectation
  simp only [hw, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_powerset]
  simp only [Finset.card_univ, Fintype.card_fin]
  refine Finset.sum_congr rfl fun l _ => ?_
  unfold levelFourier
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  rw [(Finset.mem_powersetCard.mp ht).2]
  simp only [Cotype.fourier, average, smul_eq_mul, hN, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun ε _ => ?_
  rw [one_div, inv_pow]; ring

