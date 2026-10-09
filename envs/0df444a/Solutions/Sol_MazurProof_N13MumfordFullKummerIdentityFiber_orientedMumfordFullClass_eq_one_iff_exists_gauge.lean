-- Prove2me | solution 1 for MazurProof.N13MumfordFullKummerIdentityFiber.orientedMumfordFullClass_eq_one_iff_exists_gauge
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:12:50.612285+00:00
-- url     : https://prove2.me/submissions/a80c778c-7d66-4476-a80f-cb11a4d84cd1

import Mathlib
import Definitions.Def_MazurN13_L4

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianDifferentSupport.relativeToORingEquiv_gaussianTwo
attribute [local simp] MazurProof.N13GaussianFieldEquiv.gaussianI_sq
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GaussianNamedUnitTransport.orderToGaussian_apply
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13IntegralAffinePointSpread.sexticSemi_v
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
-- ===== FLT.Assumptions.MazurProof.N13MumfordFullKummerIdentityFiber =====
section
/-!
# The remaining identity fibre of the N13 full Kummer map

The target algebra already shows that the N13 full Kummer map has one
kernel fibre.  This file unfolds that fibre instead of treating it as an
opaque equality:

* triviality in the full target is equivalent to an explicit full-gauge
  witness `(β,q)`;
* divisibility by two in the oriented Picard quotient is equivalent to an
  explicit square root of the raw oriented fractional ideal.

The remaining geometric seam is closed here by a dimension-theoretic Padé
numerator, homogeneous resultants, quadratic-algebra rigidity, and Cantor
ideal identities.  No representative enumeration or finite certificate is
used.
-/
namespace MazurProof.N13MumfordFullKummerIdentityFiber
noncomputable section
open Polynomial
open SexticMumford
open scoped nonZeroDivisors
/-! ## Unfolding the full-gauge fibre -/
/-- Equality to one in the full target is exactly membership in the product
of the square/norm and scalar/cubic gauges. -/
theorem orientedMumfordFullClass_eq_one_iff_exists_gauge
    (D : LowRep) :
    N13MumfordOrientedFullKummer.orientedMumfordFullClass D = 1 ↔
      ∃ β : Lˣ, ∃ q : ℚˣ,
        N13MumfordOrientedFullKummer.orientedMumfordNormPair D =
          EvenSexticNormPair.chi
              N13FullNormPair.normUnits β *
            EvenSexticNormPair.iota
              N13FullNormPair.normUnits
              N13FullNormPair.scalarUnits
              N13FullNormPair.normUnits_scalarUnits q := by
  constructor
  · intro hD
    have hmem :
        N13MumfordOrientedFullKummer.orientedMumfordNormPair D ∈
          EvenSexticNormPair.fullGauge
            N13FullNormPair.normUnits
            N13FullNormPair.scalarUnits
            N13FullNormPair.normUnits_scalarUnits :=
      (QuotientGroup.eq_one_iff _).mp hD
    obtain ⟨x, hx, y, hy, hxy⟩ :=
      Subgroup.mem_sup.mp hmem
    obtain ⟨β, rfl⟩ := hx
    obtain ⟨q, rfl⟩ := hy
    exact ⟨β, q, hxy.symm⟩
  · rintro ⟨β, q, hD⟩
    apply (QuotientGroup.eq_one_iff _).mpr
    rw [hD]
    apply Subgroup.mul_mem_sup
    · exact ⟨β, rfl⟩
    · exact ⟨q, rfl⟩
/-! ## The canonical polynomial square-root witness -/
/-! ## The structural Padé numerator -/
/-! ## The Cantor square behind a Padé half -/
universe u
variable {K : Type u} [Field K]
/-! ## From the sextic norm to the quadratic norm -/
/-! ## Closing the finite ideal square -/
namespace FinitePadeGraphRootData
end FinitePadeGraphRootData
namespace FiniteIdealGraphRootData
end FiniteIdealGraphRootData
/-! The branch `c = 0` is not a degenerate coefficient search.  The UFD
identity `q l² = a²u` says directly that the monic polynomial `u` is a
square; the corresponding repeated graph ideal is then the finite square
root. -/
/-! ## Squares in the oriented fractional-ideal quotient -/
/-! ## Absorbing the remaining infinity coordinate -/
/-! ## The structural full-gauge bridge -/
/-! ## Compatibility with the earlier abstract bridge interface -/
end
end MazurProof.N13MumfordFullKummerIdentityFiber
end

end

theorem solution : type_of% @MazurProof.N13MumfordFullKummerIdentityFiber.orientedMumfordFullClass_eq_one_iff_exists_gauge := @MazurProof.N13MumfordFullKummerIdentityFiber.orientedMumfordFullClass_eq_one_iff_exists_gauge
