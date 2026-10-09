-- Prove2me | solution 1 for MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_sextic_scalar
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-09T08:12:48.300974+00:00
-- url     : https://prove2.me/submissions/b4f61c1d-7887-451f-ad65-7057b04f58bf

import Mathlib
import Definitions.Def_MazurN13_L4
import Theorems.Thm_MazurProof_N13Mumford_f_monic

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
/-! ## The canonical polynomial square-root witness -/
@[simp] theorem mk_branchSquarePolynomial (β : Lˣ) :
    AdjoinRoot.mk N13SexticSquareclass.f
        (branchSquarePolynomial β) =
      (β : L) := by
  exact
    AdjoinRoot.mk_leftInverse
      sextic_f_monic (β : L)
/-- The first full-gauge coordinate is equivalently an honest polynomial
congruence modulo the sextic.  This is the algebraic input from which the
missing curve ideal square root must be constructed. -/
theorem branchSquarePolynomial_congruence
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q) :
    N13Mumford.f ℚ ∣
      D.toSemi.u -
        Polynomial.C (q : ℚ) * branchSquarePolynomial β ^ 2 := by
  change N13SexticSquareclass.f ∣
    D.toSemi.u -
      Polynomial.C (q : ℚ) * branchSquarePolynomial β ^ 2
  apply AdjoinRoot.mk_eq_zero.mp
  rw [map_sub, map_mul, map_pow, AdjoinRoot.mk_C,
    mk_branchSquarePolynomial]
  have hval :=
    congrArg (fun z : Lˣ => (z : L)) hfst
  change
    N13MumfordKummerValue.uTheta
          (N13LowDegreeKummerHom.asMumford D) =
      (β : L) ^ 2 * algebraMap ℚ L (q : ℚ) at hval
  rw [N13MumfordKummerValue.uTheta_eq_mk] at hval
  change
    AdjoinRoot.mk N13SexticSquareclass.f D.toSemi.u =
      (β : L) ^ 2 * algebraMap ℚ L (q : ℚ) at hval
  rw [hval]
  rw [AdjoinRoot.algebraMap_eq]
  ring
/-! ## The structural Padé numerator -/
/-- Killing the two high coefficients leaves a remainder of degree at most
three, since reduction modulo the monic sextic already kills every
coefficient from degree six upward. -/
theorem padeRemainder_natDegree_le_three
    (B : ℚ[X]) (a : Polynomial.degreeLT ℚ 3)
    (haKer : padeHighCoeffMap B a = 0) :
    (padeRemainderMap B a).natDegree ≤ 3 := by
  have hcoeff :=
    congrArg (fun z : ℚ × ℚ => z) haKer
  have h4 :
      (padeRemainderMap B a).coeff 4 = 0 := by
    exact congrArg Prod.fst hcoeff
  have h5 :
      (padeRemainderMap B a).coeff 5 = 0 := by
    exact congrArg Prod.snd hcoeff
  have hfne :
      N13SexticSquareclass.f ≠ 1 := by
    intro hf
    have hdegree :=
      congrArg Polynomial.natDegree hf
    change
      (N13Mumford.f ℚ).natDegree =
        (1 : ℚ[X]).natDegree at hdegree
    rw [N13Mumford.f_natDegree, natDegree_one] at hdegree
    omega
  have hrem :
      (padeRemainderMap B a).natDegree < 6 := by
    simpa only [padeRemainderMap_apply,
      N13SexticSquareclass.f,
      N13Mumford.f_natDegree] using
        (Polynomial.natDegree_modByMonic_lt
          ((a : ℚ[X]) * B) sextic_f_monic hfne)
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  by_cases hn4 : n = 4
  · simpa only [hn4] using h4
  by_cases hn5 : n = 5
  · simpa only [hn5] using h5
  have hn6 : 6 ≤ n := by omega
  exact coeff_eq_zero_of_natDegree_lt
    (hrem.trans_le hn6)
/-- The Padé kernel turns the branch-algebra congruence into a single
sextic polynomial identity.  Degree at most six makes the quotient by the
monic sextic a scalar. -/
theorem exists_pade_sextic_scalar
    (D : LowRep) (β : Lˣ) (q : ℚˣ)
    (hfst :
      N13MumfordKummerValue.uThetaUnit
            (N13LowDegreeKummerHom.asMumford D) =
        β ^ 2 * N13FullNormPair.scalarUnits q)
    (a : Polynomial.degreeLT ℚ 3)
    (ha0 : a ≠ 0)
    (haKer :
      padeHighCoeffMap
          (branchSquarePolynomial β) a = 0) :
    ∃ c : ℚ,
      Polynomial.C (q : ℚ) *
            (padeRemainderMap
              (branchSquarePolynomial β) a) ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u =
        Polynomial.C c * N13Mumford.f ℚ := by
  let f : ℚ[X] := N13Mumford.f ℚ
  let B : ℚ[X] := branchSquarePolynomial β
  let l : ℚ[X] := padeRemainderMap B a
  have hcong :
      f ∣ D.toSemi.u -
        Polynomial.C (q : ℚ) * B ^ 2 := by
    exact branchSquarePolynomial_congruence D β q hfst
  have hu :
      AdjoinRoot.mk f D.toSemi.u =
        AdjoinRoot.mk f
          (Polynomial.C (q : ℚ) * B ^ 2) :=
    (AdjoinRoot.mk_eq_mk).2 hcong
  have hl :
      AdjoinRoot.mk f l =
        AdjoinRoot.mk f ((a : ℚ[X]) * B) := by
    apply (AdjoinRoot.mk_eq_mk).2
    exact Polynomial.dvd_modByMonic_sub
      ((a : ℚ[X]) * B) f
  have hdiv :
      f ∣
        Polynomial.C (q : ℚ) * l ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u := by
    apply AdjoinRoot.mk_eq_zero.mp
    simp only [map_sub, map_mul, map_pow,
      AdjoinRoot.mk_C]
    rw [hl, hu]
    simp only [map_mul, map_pow, AdjoinRoot.mk_C]
    ring
  have haDegree :
      (a : ℚ[X]).natDegree ≤ 2 :=
    padeNumerator_natDegree_le_two a ha0
  have hlDegree :
      l.natDegree ≤ 3 :=
    padeRemainder_natDegree_le_three B a haKer
  have huDegree :
      D.toSemi.u.natDegree ≤ 2 :=
    D.degree_le_two
  have hleftDegree :
      (Polynomial.C (q : ℚ) * l ^ 2 -
          (a : ℚ[X]) ^ 2 * D.toSemi.u).natDegree ≤ 6 := by
    have hq :
        (Polynomial.C (q : ℚ)).natDegree ≤ 0 :=
      by rw [Polynomial.natDegree_C]
    have hl2 :
        (l ^ 2).natDegree ≤ 6 := by
      rw [Polynomial.natDegree_pow]
      omega
    have ha2 :
        ((a : ℚ[X]) ^ 2).natDegree ≤ 4 := by
      rw [Polynomial.natDegree_pow]
      omega
    have hfirst :
        (Polynomial.C (q : ℚ) * l ^ 2).natDegree ≤ 6 :=
      (Polynomial.natDegree_mul_le).trans
        (by omega)
    have hsecond :
        ((a : ℚ[X]) ^ 2 *
          D.toSemi.u).natDegree ≤ 6 :=
      (Polynomial.natDegree_mul_le).trans
        (by omega)
    exact (Polynomial.natDegree_sub_le _ _).trans
      (max_le hfirst hsecond)
  obtain ⟨t, ht⟩ := hdiv
  have htDegree : t.natDegree ≤ 0 := by
    by_cases ht0 : t = 0
    · simp [ht0]
    have hf0 : f ≠ 0 := by
      exact (N13Mumford.f_monic (K := ℚ)).ne_zero
    have hdegree :
        6 + t.natDegree =
          (Polynomial.C (q : ℚ) * l ^ 2 -
            (a : ℚ[X]) ^ 2 * D.toSemi.u).natDegree := by
      rw [ht, Polynomial.natDegree_mul hf0 ht0]
      simp only [f, N13Mumford.f_natDegree]
    omega
  let c : ℚ := t.coeff 0
  have htC : t = Polynomial.C c :=
    Polynomial.eq_C_of_natDegree_le_zero htDegree
  refine ⟨c, ?_⟩
  change
    Polynomial.C (q : ℚ) * l ^ 2 -
        (a : ℚ[X]) ^ 2 * D.toSemi.u =
      Polynomial.C c * f
  rw [ht, htC]
  ring
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

theorem solution : type_of% @MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_sextic_scalar := @MazurProof.N13MumfordFullKummerIdentityFiber.exists_pade_sextic_scalar
