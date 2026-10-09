-- Prove2me | solution 1 for MazurProof.N13GlobalKummerSimpleRootParity.localU_coeff_two_isUnit_of_mem_nonsimple
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T07:57:13.449634+00:00
-- url     : https://prove2.me/submissions/ebf6e280-2766-4b38-a444-5f28191b5c60

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

-- ===== FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot =====
section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
-- ===== FLT.Assumptions.MazurProof.N13GoodPrimeSimpleRoot =====
section
/-!
# The simple-root branch of the N13 denominator-prime argument

At a height-one prime away from the different, a primitive quadratic
Mumford polynomial has only two possible behaviours at the integral branch
point.  In the simple-root case, Hensel lifting gives an actual nearby root.
The value of the quadratic at the branch point is then the root difference
times a unit.  The same root difference is a square up to a unit by the
Mumford equation and the unit secant slope of the smooth sextic.

This file packages that structural argument over an arbitrary Henselian
pair.  In particular, the denominator-clearing scale is absorbed into the
square root in the fraction field; no denominator prime is enumerated.
-/
open Polynomial
open IsDedekindDomain
open IsDedekindDomain.HeightOneSpectrum
open scoped Ring
namespace MazurProof.N13GoodPrimeSimpleRoot
noncomputable section
@[simp] theorem quadratic_eval
    {R : Type*} [CommRing R] (a b c x : R) :
    (quadratic a b c).eval x =
      a * x ^ 2 + b * x + c := by
  simp [quadratic]
@[simp] theorem quadratic_derivative_eval
    {R : Type*} [CommRing R] (a b c x : R) :
    (quadratic a b c).derivative.eval x =
      2 * a * x + b := by
  simp [quadratic]
  ring
/-- Every polynomial of degree at most two is recovered from its first
three coefficients. -/
theorem eq_quadratic_of_natDegree_le_two
    {R : Type*} [CommRing R]
    (p : R[X]) (hdeg : p.natDegree ≤ 2) :
    p = quadratic (p.coeff 2) (p.coeff 1) (p.coeff 0) := by
  ext n
  by_cases hn0 : n = 0
  · subst n
    simp [quadratic]
  by_cases hn1 : n = 1
  · subst n
    simp [quadratic]
  by_cases hn2 : n = 2
  · subst n
    simp [quadratic]
  have hn : 2 < n := by omega
  have hpzero :
      p.coeff n = 0 :=
    coeff_eq_zero_of_natDegree_lt
      (hdeg.trans_lt hn)
  rw [hpzero]
  simp [quadratic, coeff_C, coeff_X, coeff_X_pow,
    hn0, hn2, Ne.symm hn1]
/-- Structural isolation of the remaining quadratic regime.

In a local ring, a degree-at-most-two polynomial whose coefficients generate
the unit ideal cannot be both small and nonsimple unless its quadratic
coefficient is a unit.  Thus the only branch not handled by the simple-root
theorem is the leading-unit double-root branch. -/
theorem coeff_two_isUnit_of_content_top_small_nonsimple
    {R : Type*} [CommRing R] [IsLocalRing R]
    (p : R[X]) (hdeg : p.natDegree ≤ 2)
    (hcontent : p.contentIdeal = ⊤)
    (x : R)
    (hsmall :
      p.eval x ∈ IsLocalRing.maximalIdeal R)
    (hnonsimple :
      ¬ IsUnit (p.derivative.eval x)) :
    IsUnit (p.coeff 2) := by
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  by_contra ha_unit
  have hp :
      p = quadratic a b c := by
    simpa only [a, b, c] using
      eq_quadratic_of_natDegree_le_two p hdeg
  have ha_mem :
      a ∈ IsLocalRing.maximalIdeal R := by
    simpa only [IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff] using ha_unit
  have hderiv_mem :
      2 * a * x + b ∈
        IsLocalRing.maximalIdeal R := by
    have h :=
      (show
        p.derivative.eval x ∈
          IsLocalRing.maximalIdeal R by
        simpa only [IsLocalRing.mem_maximalIdeal,
          mem_nonunits_iff] using hnonsimple)
    rw [hp] at h
    simpa using h
  have hax_mem :
      2 * a * x ∈
        IsLocalRing.maximalIdeal R := by
    have :=
      (IsLocalRing.maximalIdeal R).mul_mem_left
        (2 * x) ha_mem
    convert this using 1
    all_goals ring
  have hb_mem :
      b ∈ IsLocalRing.maximalIdeal R := by
    have :=
      (IsLocalRing.maximalIdeal R).sub_mem
        hderiv_mem hax_mem
    convert this using 1
    all_goals ring
  have hsmall' :
      a * x ^ 2 + b * x + c ∈
        IsLocalRing.maximalIdeal R := by
    rw [hp] at hsmall
    simpa using hsmall
  have hax2_mem :
      a * x ^ 2 ∈
        IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).mul_mem_right
      (x ^ 2) ha_mem
  have hbx_mem :
      b * x ∈
        IsLocalRing.maximalIdeal R :=
    (IsLocalRing.maximalIdeal R).mul_mem_right
      x hb_mem
  have hc_mem :
      c ∈ IsLocalRing.maximalIdeal R := by
    have :=
      (IsLocalRing.maximalIdeal R).sub_mem
        ((IsLocalRing.maximalIdeal R).sub_mem
          hsmall' hax2_mem)
        hbx_mem
    convert this using 1
    all_goals ring
  have hle :
      p.contentIdeal ≤
        IsLocalRing.maximalIdeal R := by
    rw [Polynomial.contentIdeal_def,
      Ideal.span_le]
    intro z hz
    obtain ⟨n, -, rfl⟩ :=
      Polynomial.mem_coeffs_iff.mp hz
    rw [hp]
    by_cases hn0 : n = 0
    · subst n
      simpa [quadratic] using hc_mem
    by_cases hn1 : n = 1
    · subst n
      simpa [quadratic] using hb_mem
    by_cases hn2 : n = 2
    · subst n
      simpa [quadratic] using ha_mem
    simp [quadratic, coeff_C, coeff_X, coeff_X_pow,
      hn0, hn2, Ne.symm hn1]
  have htop :
      (⊤ : Ideal R) ≤
        IsLocalRing.maximalIdeal R := by
    rw [← hcontent]
    exact hle
  exact
    (IsLocalRing.maximalIdeal.isMaximal R).ne_top
      (top_unique htop)
end
end MazurProof.N13GoodPrimeSimpleRoot
end

end

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
theorem localU_eval_localTheta
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (localU D P).eval (localTheta P) =
      algebraMap O (LocalIntegers P)
        (normalizedKummerInteger D) := by
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
theorem localU_natDegree_le
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (localU D P).natDegree ≤ 2 :=
  Polynomial.natDegree_map_le.trans
    (normalizedKummerInteger_degree D)
/-- Global primitivity remains the statement that the local coefficients
generate the unit ideal. -/
theorem localU_contentIdeal_eq_top
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O) :
    (localU D P).contentIdeal = ⊤ := by
  rw [localU, localPolynomial,
    Polynomial.contentIdeal_map_eq_map_contentIdeal]
  have hprimitive :=
    primitiveNormalization_isPrimitive D.toSemi.u
  have htop :
      (primitiveNormalization D.toSemi.u).contentIdeal =
        ⊤ :=
    (Polynomial.isPrimitive_iff_contentIdeal_eq_top
      (primitiveNormalization D.toSemi.u)).mp
      hprimitive
  rw [htop, Ideal.map_top]
/-- In the nonsimple branch, local primitivity forces the leading
coefficient to be a unit.  This isolates the sole remaining local case. -/
theorem localU_coeff_two_isUnit_of_mem_nonsimple
    (D : N13LowDegreeKummerHom.LowRep)
    (P : HeightOneSpectrum O)
    (hmem :
      normalizedKummerInteger D ∈ P.asIdeal)
    (hnonsimple :
      ¬ IsUnit
        ((localU D P).derivative.eval
          (localTheta P))) :
    IsUnit ((localU D P).coeff 2) := by
  apply
    coeff_two_isUnit_of_content_top_small_nonsimple
      (localU D P)
      (localU_natDegree_le D P)
      (localU_contentIdeal_eq_top D P)
      (localTheta P)
  · rw [localU_eval_localTheta]
    exact
      (algebraMap_mem_completionIdeal_iff P _).mpr
        hmem
  · exact hnonsimple
end
end MazurProof.N13GlobalKummerSimpleRootParity
end

end

theorem solution : type_of% @MazurProof.N13GlobalKummerSimpleRootParity.localU_coeff_two_isUnit_of_mem_nonsimple := @MazurProof.N13GlobalKummerSimpleRootParity.localU_coeff_two_isUnit_of_mem_nonsimple
