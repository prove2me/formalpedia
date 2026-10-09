-- Prove2me | solution 1 for MazurProof.N13GlobalKummerSimpleRootParity.localF_derivative_isUnit
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T06:39:38.986185+00:00
-- url     : https://prove2.me/submissions/39c143ad-b378-4193-858f-32d5df24d931

import Mathlib
import Definitions.Def_MazurN13_L3

set_option maxHeartbeats 1000000
attribute [local simp] MazurProof.N13GaussianFractionField.gaussianBasis_apply
attribute [local simp] MazurProof.N13GaussianGlobalArithmetic.h_coeff_zero
attribute [local simp] MazurProof.N13GeneralizedMumfordIntegral.yClass_relation
attribute [local simp] MazurProof.N13GoodCoordinateRingTwo.yClass_relation
attribute [local simp] MazurProof.N13GoodSexticMumfordTransport.toSextic_ySubClass
attribute [local simp] MazurProof.N13Infinity.reverseTail_constantCoeff
attribute [local simp] MazurProof.N13LaurentPolynomialOrder.parameter_inv
attribute [local simp] MazurProof.N13SpecialQuotientBasis.specialData_u_natDegree

-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerSimpleRootParity =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GlobalKummerSimpleRootParity =====
section
/-!
# Simple-root parity for normalized N13 Kummer values

This file maps the primitive global Mumford polynomial and its homogeneous
curve relation into the integer ring of a height-one completion.  Away from
the different, the sextic secant is a unit.  Hence whenever the quadratic
Mumford polynomial has a simple root modulo the prime, its normalized
Kummer value has even multiplicity.

The denominator-clearing scale is not inverted in the integer ring.  It is
absorbed into the square root only after passing to the completion field,
so no denominator prime is excluded.
-/
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped nonZeroDivisors
namespace MazurProof.N13GlobalKummerSimpleRootParity
noncomputable section
open N13GlobalKummerNormalization
open N13GlobalKummerIdealSquare
open N13GoodPrimeSimpleRoot
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.fieldL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.dedekindO
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.fractionRingOL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.charZeroL
attribute [local instance] MazurProof.N13GlobalKummerSimpleRootParity.charZeroCompletion
/-- Evaluation at the local branch point commutes with the map from the
global ring of integers. -/
theorem localPolynomial_eval_localTheta
    (P : HeightOneSpectrum O) (p : ℤ[X]) :
    (localPolynomial P p).eval (localTheta P) =
      algebraMap O (LocalIntegers P)
        (integralEval p) := by
  rw [localPolynomial, Polynomial.eval_map]
  change
    eval₂ (algebraMap ℤ (LocalIntegers P))
        (algebraMap O (LocalIntegers P) integralTheta) p =
      algebraMap O (LocalIntegers P)
        (eval₂ (algebraMap ℤ O) integralTheta p)
  have h :=
    (Polynomial.hom_eval₂ p
      (algebraMap ℤ O)
      (algebraMap O (LocalIntegers P))
      integralTheta).symm
  have hmaps :
      (algebraMap O (LocalIntegers P)).comp
          (algebraMap ℤ O) =
        algebraMap ℤ (LocalIntegers P) :=
    RingHom.ext_int _ _
  rw [← hmaps]
  exact h
/-- The local derivative is the image of the global different generator. -/
theorem localF_derivative_eval_localTheta
    (P : HeightOneSpectrum O) :
    (localF P).derivative.eval (localTheta P) =
      algebraMap O (LocalIntegers P)
        (integralEval
          N13SexticIrreducible.fInt.derivative) := by
  rw [localF, localPolynomial, derivative_map]
  exact localPolynomial_eval_localTheta P _
/-- The completion ideal lies over the original height-one prime. -/
theorem algebraMap_mem_completionIdeal_iff
    (P : HeightOneSpectrum O) (x : O) :
    algebraMap O (LocalIntegers P) x ∈
        P.completionIdeal L ↔
      x ∈ P.asIdeal := by
  change
    x ∈ Ideal.comap
        (algebraMap O (LocalIntegers P))
        (P.completionIdeal L) ↔
      x ∈ P.asIdeal
  have hover :
      Ideal.comap
          (algebraMap O (LocalIntegers P))
          (P.completionIdeal L) =
        P.asIdeal :=
    by
      simpa only [Ideal.under_def] using
        (inferInstance :
          (P.completionIdeal L).LiesOver P.asIdeal).over.symm
  rw [hover]
/-- An element avoiding the global prime maps to a local unit. -/
theorem localMap_isUnit_iff_not_mem
    (P : HeightOneSpectrum O) (x : O) :
    IsUnit (algebraMap O (LocalIntegers P) x) ↔
      x ∉ P.asIdeal := by
  have hmem :=
    algebraMap_mem_completionIdeal_iff P x
  have hnonunit :
      algebraMap O (LocalIntegers P) x ∈
          P.completionIdeal L ↔
        ¬ IsUnit
          (algebraMap O (LocalIntegers P) x) := by
    simp only [IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  tauto
/-- Away from the different, the local sextic derivative is a unit. -/
theorem localF_derivative_isUnit
    (P : HeightOneSpectrum O)
    (hdifferent :
      integralEval
          N13SexticIrreducible.fInt.derivative ∉
        P.asIdeal) :
    IsUnit
      ((localF P).derivative.eval
        (localTheta P)) := by
  rw [localF_derivative_eval_localTheta]
  exact
    (localMap_isUnit_iff_not_mem P _).mpr
      hdifferent
end
end MazurProof.N13GlobalKummerSimpleRootParity
end

end

theorem solution : type_of% @MazurProof.N13GlobalKummerSimpleRootParity.localF_derivative_isUnit := @MazurProof.N13GlobalKummerSimpleRootParity.localF_derivative_isUnit
