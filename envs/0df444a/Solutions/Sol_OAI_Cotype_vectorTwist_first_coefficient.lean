-- Prove2me | solution 1 for OAI.Cotype.vectorTwist_first_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:27:47.881585+00:00
-- url     : https://prove2.me/submissions/e4224960-cd56-4c7d-9453-9d73754a3dbd

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

open OAI OAI.Cotype
open scoped BigOperators
variable {α : Type*} [Fintype α]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
theorem h50f_neg_char {ι : Type*} [Fintype ι] [DecidableEq ι] (p ε : ι → Bool) :
    character p (negateCube ε) = paritySign p * character p ε := by
  unfold character paritySign negateCube
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases p i <;> cases ε i <;> simp

theorem h50f_odd {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) (p : ι → Bool) :
    fourier (oddPart f) p = (1 - paritySign p) / 2 * fourier f p := by
  have hsub : ∑ ε, f (negateCube ε) * character p ε = paritySign p * ∑ ε, f ε * character p ε := by
    rw [← Equiv.sum_comp negateEquiv]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_
    show f (negateCube (negateCube ε)) * character p (negateCube ε) = _
    rw [negateCube_negateCube, h50f_neg_char]; ring
  simp only [Cotype.fourier, average, smul_eq_mul, oddPart]
  have : ∑ ε, (f ε - f (negateCube ε)) / 2 * character p ε =
      (∑ ε, f ε * character p ε - ∑ ε, f (negateCube ε) * character p ε) / 2 := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun ε _ => ?_; ring
  rw [this, hsub]; ring

theorem solution {m : ℕ} (φ : Cube m → Cube m → ℝ)
    (c : ℝ) (hm : ∀ s i, moment ℝ (φ s) i = c * sign (s i)) (i : Fin m) :
    fourier (oddPart (vectorTwist φ)) (unitIndex i) = c := by
  rw [h50f_odd]
  have hp : paritySign (unitIndex i) = -1 := by
    unfold paritySign unitIndex
    rw [Finset.prod_eq_single i (fun j _ hj => by simp [Ne.symm hj]) (by simp)]
    simp
  rw [hp]
  norm_num
  simp only [Cotype.fourier, vectorTwist, average, smul_eq_mul, character_unitIndex, Finset.sum_mul]
  have hsub : ∀ ε : Cube m, ∑ s : Cube m, (Fintype.card (Cube m) : ℝ)⁻¹ * φ (xorCube ε s) ε * sign (s i)
      = ∑ t : Cube m, (Fintype.card (Cube m) : ℝ)⁻¹ * φ t ε * (sign (ε i) * sign (t i)) := by
    intro ε
    let e : Cube m ≃ Cube m := ⟨xorCube ε, xorCube ε, fun s => by funext j; simp [xorCube],
      fun s => by funext j; simp [xorCube]⟩
    rw [← Equiv.sum_comp e]
    refine Finset.sum_congr rfl fun t _ => ?_
    have : xorCube ε (xorCube ε t) = t := by funext j; simp [xorCube]
    simp only [e, Equiv.coe_fn_mk, this]
    congr 1
    simp [xorCube, sign_xor]
  have hmom : ∀ t : Cube m, ∑ ε : Cube m, (Fintype.card (Cube m) : ℝ)⁻¹ * φ t ε * sign (ε i) =
      c * sign (t i) := by
    intro t
    rw [← hm t i]
    simp only [moment, average, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ε _ => ?_; ring
  have hss : ∀ t : Cube m, sign (t i) * sign (t i) = 1 := fun t => sign_sq _
  simp only [Finset.mul_sum]
  calc ∑ s : Cube m, (Fintype.card (Cube m) : ℝ)⁻¹ *
        ((∑ ε : Cube m, (Fintype.card (Cube m) : ℝ)⁻¹ * φ (xorCube ε s) ε) * sign (s i))
      = (Fintype.card (Cube m) : ℝ)⁻¹ * ∑ ε : Cube m, ∑ s : Cube m,
          (Fintype.card (Cube m) : ℝ)⁻¹ * φ (xorCube ε s) ε * sign (s i) := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
    _ = (Fintype.card (Cube m) : ℝ)⁻¹ * ∑ t : Cube m, sign (t i) * ∑ ε : Cube m,
          (Fintype.card (Cube m) : ℝ)⁻¹ * φ t ε * sign (ε i) := by
        simp only [hsub, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun ε _ => ?_; ring
    _ = c := by
        simp only [hmom]
        have : ∀ t : Cube m, sign (t i) * (c * sign (t i)) = c := fun t => by
          rw [mul_left_comm, hss, mul_one]
        simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        have hN : (Fintype.card (Cube m) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        field_simp

