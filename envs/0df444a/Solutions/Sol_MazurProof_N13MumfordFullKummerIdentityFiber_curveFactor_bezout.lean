-- Prove2me | solution 1 for MazurProof.N13MumfordFullKummerIdentityFiber.curveFactor_bezout
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T05:01:38.513197+00:00
-- url     : https://prove2.me/submissions/b0088d2e-8f77-46e9-adf5-d6611755491e

import Mathlib
import Definitions.Def_MazurN13_L2

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
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
/-! ## The canonical polynomial square-root witness -/
/-! ## The structural Padé numerator -/
/-! ## The Cantor square behind a Padé half -/
universe u
variable {K : Type u} [Field K]
/-! ## From the sextic norm to the quadratic norm -/
/-- If `f - L² = a w`, the complementary graph ideal is contained in
`(a,Y-L)` whenever `a ∣ w`.  Cantor's product formula then supplies the
missing generator `Y-L` of the square.  Thus no factorization of `a` is
needed. -/
theorem curveFactor_bezout
    (C : SexticMumford.Model K) (u₀ w L₀ : K[X])
    (hu₀ : u₀ ≠ 0)
    (hcurve : C.f - L₀ ^ 2 = u₀ * w) :
    ∃ A B E : K[X],
      A * u₀ + B * (2 * L₀) + E * w = 1 := by
  classical
  have hcop :
      IsCoprime u₀
        (EuclideanDomain.gcd (2 * L₀) w) := by
    apply isCoprime_of_irreducible_dvd
    · intro hzero
      exact hu₀ hzero.1
    · intro z hz hzu hzg
      have hz2L : z ∣ 2 * L₀ :=
        hzg.trans
          (EuclideanDomain.gcd_dvd_left (2 * L₀) w)
      have hzw : z ∣ w :=
        hzg.trans
          (EuclideanDomain.gcd_dvd_right (2 * L₀) w)
      have htwo : IsUnit (2 : K[X]) := by
        have heq :
            Polynomial.C (2 : K) = (2 : K[X]) := by
          exact map_natCast
            (Polynomial.C : K →+* K[X]) 2
        rw [← heq]
        exact isUnit_C.mpr
          (isUnit_iff_ne_zero.mpr C.two_ne_zero)
      have hzL : z ∣ L₀ := by
        rcases hz.prime.dvd_mul.mp hz2L with hz2 | hzL
        · exact
            (hz.not_isUnit
              (isUnit_of_dvd_unit hz2 htwo)).elim
        · exact hzL
      have hzzSub : z * z ∣ C.f - L₀ ^ 2 := by
        rw [hcurve]
        exact mul_dvd_mul hzu hzw
      have hzzSq : z * z ∣ L₀ ^ 2 := by
        simpa only [pow_two] using
          mul_dvd_mul hzL hzL
      have hzzF : z * z ∣ C.f := by
        simpa only [sub_add_cancel] using
          dvd_add hzzSub hzzSq
      exact
        ((squarefree_iff_irreducible_sq_not_dvd_of_ne_zero
          C.ne_zero).mp C.squarefree z hz) hzzF
  obtain ⟨A, T, hAT⟩ := hcop
  refine
    ⟨A,
      T * EuclideanDomain.gcdA (2 * L₀) w,
      T * EuclideanDomain.gcdB (2 * L₀) w, ?_⟩
  rw [← hAT, EuclideanDomain.gcd_eq_gcd_ab]
  ring
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

theorem solution : type_of% @MazurProof.N13MumfordFullKummerIdentityFiber.curveFactor_bezout := @MazurProof.N13MumfordFullKummerIdentityFiber.curveFactor_bezout
