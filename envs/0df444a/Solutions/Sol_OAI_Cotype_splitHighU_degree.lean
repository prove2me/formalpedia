-- Prove2me | solution 1 for OAI.Cotype.splitHighU_degree
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:24:11.466408+00:00
-- url     : https://prove2.me/submissions/d549b0a0-decf-45f5-b503-0c380db0cc80

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

open OAI OAI.Cotype
open scoped BigOperators
open Polynomial Polynomial.Chebyshev
variable {m : ℕ}
theorem h50x_cheb (Q : ℝ[X]) (d : ℕ) (hdeg : Q.degree ≤ d) :
    ∃ c : Fin (d+1) → ℝ, ∑ j, c j • T ℝ (j : ℕ) = Q := by
  have hQ : Q ∈ degreeLE ℝ d := mem_degreeLE.mpr hdeg
  rw [← Sequence.span_degreeLE (chebyshevTsequence ℝ) (fun i _ => by simp)] at hQ
  have himg : (chebyshevTsequence ℝ) '' Set.Iic d = Set.range (fun j : Fin (d+1) => T ℝ (j : ℕ)) := by
    ext p; simp only [Set.mem_image, Set.mem_Iic, Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩; exact ⟨⟨i, by omega⟩, by simp [chebyshevTsequence]⟩
    · rintro ⟨j, rfl⟩; exact ⟨j, by omega, by simp [chebyshevTsequence]⟩
  rw [himg] at hQ
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).mp hQ

theorem h50x_low (d k : ℕ) (hk : k ≤ d) : chebLow d ((X : ℝ[X]) ^ k) = X ^ k := by
  obtain ⟨c, hc⟩ := h50x_cheb ((X : ℝ[X]) ^ k) k (by rw [degree_X_pow])
  rw [← hc, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, chebLow_basis, if_pos (by omega)]

theorem solution (f : SignMatrix m → ℝ) (d : ℕ) (s : ℝ) :
    (splitHighU f d s).degree ≤ d := by
  rw [← mem_degreeLE]
  unfold splitHighU
  refine Submodule.sum_mem _ fun k _ => Submodule.sum_mem _ fun l _ => ?_
  by_cases hl : l ≤ d
  · exact Submodule.smul_mem _ _ (mem_degreeLE.mpr ((degree_X_pow_le l).trans (by exact_mod_cast hl)))
  · have hz : retainedCoefficient f d k l * (((X : ℝ[X]) ^ k - chebLow d (X ^ k)).eval s) = 0 := by
      unfold retainedCoefficient
      by_cases hk : k ≤ d
      · rw [h50x_low d k hk, sub_self, eval_zero, mul_zero]
      · rw [if_neg (by omega), zero_mul]
    rw [hz, zero_smul]
    exact Submodule.zero_mem _

