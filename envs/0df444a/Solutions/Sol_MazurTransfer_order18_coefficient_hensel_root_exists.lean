-- Prove2me | solution 1 for MazurTransfer.order18_coefficient_hensel_root_exists
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T17:54:47.368081+00:00
-- url     : https://prove2.me/submissions/735a56d6-2765-4639-b5b9-e1404978b401

import Theorems.Thm_MazurTransfer_order18_coefficient_dyadic_prime_certificate
import Mathlib
import Definitions.Def_MazurTransfer_Order18CoefficientCompletionData
import Definitions.Def_MazurTransfer_Order18CoefficientIntegerData
import Definitions.Def_MazurTransfer_Order18MinimalHalvingData
import Definitions.Def_MazurTransfer_Order18KernelGeneratorSupportCertificate
import Theorems.Thm_MazurTransfer_order18_original_generator_support_certificate
import Theorems.Thm_MazurTransfer_order18_original_global_norm_kernel_enumeration
import Theorems.Thm_MazurTransfer_order18_original_kernel_representative_injective
import Definitions.Def_MazurTransfer_Order18AmbientSelmer
import Theorems.Thm_MazurTransfer_order18_rational_cubics_irreducible
import Theorems.Thm_MazurTransfer_order18_relative_two_division_irreducible
import Theorems.Thm_MazurTransfer_order18_compositum_integers_principal
import Theorems.Thm_MazurTransfer_order18_supported_selmer_cardinality_256
import Theorems.Thm_MazurTransfer_order18_actual_dyadic_valuation_certificate
import Theorems.Thm_MazurTransfer_order18_normalized_cubic_unique_root
import Theorems.Thm_MazurTransfer_order18_dyadic_candidate_nonsquare
open scoped WeierstrassCurve WeierstrassCurve.Affine
namespace MazurTorsion.XOneEighteenRealCubicQuotient
theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial :=
  MazurTransfer.order18_rational_cubics_irreducible.1
end MazurTorsion.XOneEighteenRealCubicQuotient
namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic
theorem twoDivisionPolynomial_irreducible : Irreducible twoDivisionPolynomial :=
  MazurTransfer.order18_rational_cubics_irreducible.2
end MazurTorsion.XOneEighteenTwoDivisionArithmetic
namespace MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
theorem relativePolynomial_irreducible : Irreducible relativePolynomial :=
  MazurTransfer.order18_relative_two_division_irreducible
end MazurTorsion.XOneEighteenTwoDivisionClassNumber
namespace MazurTorsion.XOneEighteenTwoDivisionClassNumberOne
theorem compositumRingOfIntegers_isPrincipal :
    IsPrincipalIdealRing (NumberField.RingOfIntegers MazurTorsion.XOneEighteenTwoDivisionArithmetic.M) :=
  MazurTransfer.order18_compositum_integers_principal
end MazurTorsion.XOneEighteenTwoDivisionClassNumberOne
namespace MazurTorsion.XOneEighteenGlobalSelmerBridge
theorem natCard_dyadicSelmerM
    (hprincipal : IsPrincipalIdealRing (NumberField.RingOfIntegers MazurTorsion.XOneEighteenTwoDivisionArithmetic.M))
    (V : DyadicValuationCertificate) : Nat.card DyadicSelmerM = 256 :=
  MazurTransfer.order18_supported_selmer_cardinality_256
end MazurTorsion.XOneEighteenGlobalSelmerBridge
namespace MazurTorsion.XOneEighteenDyadicValuationCertificate
noncomputable def dyadicValuationCertificate :
    MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicValuationCertificate :=
  Classical.choice MazurTransfer.order18_actual_dyadic_valuation_certificate
end MazurTorsion.XOneEighteenDyadicValuationCertificate
namespace MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate
theorem normalizedRelativeCubicValue_eq_zero_iff :
    ∀ z : Fin 3 → R, normalizedRelativeCubicValue z = 0 ↔
      z = MazurTorsion.XOneEighteenDyadicGeneratorCertificate.normalizedGenerator :=
  MazurTransfer.order18_normalized_cubic_unique_root
end MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate
namespace MazurTorsion.XOneEighteenDyadicCubicCertificate
theorem candidate_nonsquare : ∀ i : Fin 15, ¬ IsSquare (candidate i) :=
  MazurTransfer.order18_dyadic_candidate_nonsquare
end MazurTorsion.XOneEighteenDyadicCubicCertificate
namespace MazurTorsion.XOneEighteenQuotientRankZero
end MazurTorsion.XOneEighteenQuotientRankZero
namespace MazurTorsion.XOneEighteenQuotientReductionAtSeventeen
end MazurTorsion.XOneEighteenQuotientReductionAtSeventeen

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicPrime
end MazurTorsion.XOneEighteenTwoDivisionTriadicPrime
namespace MazurTorsion.XOneEighteenGlobalSelmerBridge
private theorem h1_ne_zero : MazurTorsion.XOneEighteenTwoDivisionArithmetic.h1 ≠ 0 :=
  MazurTransfer.order18_selmer_representatives_nonzero.2.2.1
private theorem h2_ne_zero : MazurTorsion.XOneEighteenTwoDivisionArithmetic.h2 ≠ 0 :=
  MazurTransfer.order18_selmer_representatives_nonzero.2.2.2.1
private theorem h3_ne_zero : MazurTorsion.XOneEighteenTwoDivisionArithmetic.h3 ≠ 0 :=
  MazurTransfer.order18_selmer_representatives_nonzero.2.2.2.2.1
private theorem h4_ne_zero : MazurTorsion.XOneEighteenTwoDivisionArithmetic.h4 ≠ 0 :=
  MazurTransfer.order18_selmer_representatives_nonzero.2.2.2.2.2
end MazurTorsion.XOneEighteenGlobalSelmerBridge

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralModel
end MazurTorsion.XOneEighteenTwoDivisionIntegralModel
namespace MazurTorsion.XOneEighteenDyadicKernelSeparation
theorem kernelRepresentative_injective : Function.Injective
    MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative :=
  MazurTransfer.order18_original_kernel_representative_injective
end MazurTorsion.XOneEighteenDyadicKernelSeparation

namespace MazurTorsion.XOneEighteenDescent
private noncomputable abbrev concreteKernelSupportCertificate :
    MazurTorsion.XOneEighteenGlobalSelmerBridge.KernelGeneratorSupportCertificate :=
  Classical.choice MazurTransfer.order18_original_generator_support_certificate
end MazurTorsion.XOneEighteenDescent



namespace MazurTorsion.XOneEighteenDyadicCompletionBridge
end MazurTorsion.XOneEighteenDyadicCompletionBridge

namespace MazurTorsion.XOneEighteenKernelGeneratorSupport
end MazurTorsion.XOneEighteenKernelGeneratorSupport

namespace MazurTorsion.XOneEighteenFinalRankZero
end MazurTorsion.XOneEighteenFinalRankZero

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralElements
end MazurTorsion.XOneEighteenTwoDivisionIntegralElements

namespace MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
end MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicLift
end MazurTorsion.XOneEighteenTwoDivisionTriadicLift

namespace MazurTorsion.XOneEighteenDyadicLocalImage
end MazurTorsion.XOneEighteenDyadicLocalImage
namespace MazurTorsion.XOneEighteenDyadicCompletionBridge
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
private theorem coefficient_not_dvd_exponent_two :
    ¬ 2 ∣ _root_.RingOfIntegers.exponent coefficientInteger :=
  MazurTransfer.order18_coefficient_dyadic_prime_certificate.1
private theorem coefficientPolynomialInt_mem_monicFactors_two :
    coefficientPolynomialInt.map (Int.castRingHom (ZMod 2)) ∈
      _root_.RingOfIntegers.monicFactorsMod coefficientInteger 2 :=
  MazurTransfer.order18_coefficient_dyadic_prime_certificate.2
end MazurTorsion.XOneEighteenDyadicCompletionBridge


/- Source module: EllipticCurves.Mathlib.AdicCompletionExtension. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Local structure of an adic completion

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

Let `A` be a Dedekind domain with fraction field `K`, and let `v` be a height-one prime of
`A`. This file provides

* `IsDedekindDomain.HeightOneSpectrum.valuation_maximalIdeal_adicCompletionIntegers`:
  the valuation associated to the height-one prime of the ring of integers `𝒪_v` (a discrete
  valuation ring) of a completion `K_v` is the valuation of the completion;
* the residue-field equivalence `A ⧸ v ≃+* 𝒪_v ⧸ 𝔪_v`;
* `IsDedekindDomain.HeightOneSpectrum.henselianLocalRing_adicCompletionIntegers` (and the
  instances leading up to it): the subspace topology on `𝒪_v` is the `𝔪`-adic topology
  (`isAdic_maximalIdeal_adicCompletionIntegers`, via `mem_maximalIdeal_pow_iff`), `𝒪_v` is
  complete, hence `𝔪`-adically complete, hence a Henselian local ring.
-/

section

open Polynomial IsDedekindDomain WithZero

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

/-- An irreducible element of the ring of integers of a completion has valuation `exp (-1)`. -/
theorem valued_irreducible_adicCompletionIntegers {π : v.adicCompletionIntegers K}
    (hπ : Irreducible π) :
    Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) π) = exp (-1) := by
  have hgen : IsLocalRing.maximalIdeal (Valued.v : Valuation (v.adicCompletion K)
      ℤᵐ⁰).valuationSubring = Ideal.span {π} := hπ.maximalIdeal_eq
  have huni := Valuation.isUniformizer_of_maximalIdeal_eq_span
    (v := (Valued.v : Valuation (v.adicCompletion K) ℤᵐ⁰)) hgen
  rwa [Valuation.IsUniformizer.iff,
    Valuation.IsRankOneDiscrete.generator_eq_exp_neg_one_of_surjective
      (v.valuedAdicCompletion_surjective K)] at huni



/-- An element of the ring of integers of a completion of valuation `exp (-e)` generates the
`e`-th power of the maximal ideal. -/
theorem span_singleton_eq_maximalIdeal_pow {x : v.adicCompletionIntegers K} {e : ℕ}
    (hx : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) x) =
      exp (-(e : ℤ))) :
    Ideal.span {x} = IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ e := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    rw [map_zero, map_zero] at hx
    exact absurd hx.symm exp_ne_zero
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hu2 : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (u : v.adicCompletionIntegers K)) = 1 :=
    (Valuation.valuationSubring.integers (v := Valued.v)).valuation_unit u
  have hval : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)
      (↑u * π ^ n)) = exp (-(n : ℤ)) := by
    rw [map_mul, map_mul, hu2, one_mul, map_pow, map_pow,
      v.valued_irreducible_adicCompletionIntegers hπ, ← exp_nsmul]
    simp
  rw [hval, exp_inj, neg_inj, Int.natCast_inj] at hx
  subst hx
  rw [Ideal.span_singleton_eq_span_singleton.mpr (associated_unit_mul_left _ _ u.isUnit),
    ← Ideal.span_singleton_pow, hπ.maximalIdeal_eq]











/-- An element of `𝒪_v` lies in the `n`-th power of the maximal ideal exactly when its
valuation is at most `exp (-n)`. -/
theorem mem_maximalIdeal_pow_iff {x : v.adicCompletionIntegers K} {n : ℕ} :
    x ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔
      Valued.v (x : v.adicCompletion K) ≤ exp (-(n : ℤ)) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (v.adicCompletionIntegers K)
  have hπn : Valued.v (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K) (π ^ n)) =
      exp (-(n : ℤ)) := by
    rw [map_pow, map_pow, v.valued_irreducible_adicCompletionIntegers hπ, ← exp_nsmul]
    simp
  rw [← span_singleton_eq_maximalIdeal_pow v hπn, Ideal.mem_span_singleton]
  have hint := Valuation.valuationSubring.integers (v := (Valued.v : Valuation
    (v.adicCompletion K) ℤᵐ⁰))
  exact ⟨fun h ↦ (hint.le_of_dvd h).trans hπn.le, fun h ↦ hint.dvd_of_le (h.trans_eq hπn.symm)⟩

/-- An element of `R` lies in `v ^ n` exactly when its image in `𝒪_v` lies in `𝔪 ^ n`:
passing to the completion changes neither the valuation nor the `v`-adic filtration of `R`. -/
theorem algebraMap_mem_maximalIdeal_pow_iff {r : R} {n : ℕ} :
    algebraMap R (v.adicCompletionIntegers K) r
        ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n ↔ r ∈ v.asIdeal ^ n := by
  rw [mem_maximalIdeal_pow_iff, algebraMap_adicCompletionIntegers_apply,
    valuedAdicCompletion_eq_valuation', valuation_of_algebraMap, intValuation_le_pow_iff_mem]

instance isTopologicalRing_adicCompletionIntegers :
    IsTopologicalRing (v.adicCompletionIntegers K) :=
  inferInstanceAs (IsTopologicalRing
    (Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring)

/-- The subspace topology on the ring of integers `𝒪_v` of an adic completion is the
`𝔪`-adic topology of its maximal ideal. -/
theorem isAdic_maximalIdeal_adicCompletionIntegers :
    IsAdic (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)) := by
  rw [isAdic_iff]
  constructor
  · -- each `𝔪 ^ n` is open: it is the preimage of a closed ball
    intro n
    obtain ⟨z, hz⟩ := v.valuedAdicCompletion_surjective K (exp (-(n : ℤ)))
    have hr0 : Valued.v.restrict z ≠ 0 := by
      intro h
      have h0 : Valued.v z = 0 := by rw [← Valuation.embedding_restrict, h, map_zero]
      rw [hz] at h0
      exact exp_ne_zero h0
    have : ((IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :
          Ideal (v.adicCompletionIntegers K)) : Set (v.adicCompletionIntegers K)) =
        (fun x : v.adicCompletionIntegers K ↦ (x : v.adicCompletion K)) ⁻¹'
          {y | Valued.v.restrict y ≤ Valued.v.restrict z} := by
      ext x
      rw [Set.mem_preimage, Set.mem_setOf, Valuation.restrict_le_iff_le_embedding,
        Valuation.embedding_restrict, hz]
      exact v.mem_maximalIdeal_pow_iff (K := K)
    rw [this]
    exact (Valued.isOpen_closedBall _ hr0).preimage continuous_subtype_val
  · -- each neighbourhood of `0` contains some `𝔪 ^ n`
    intro s hs
    obtain ⟨t, ht, hts⟩ := mem_nhds_subtype _ _ _ |>.mp hs
    rw [ZeroMemClass.coe_zero] at ht
    obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp ht
    obtain ⟨m, hm⟩ : ∃ m : ℤ, exp m < MonoidWithZeroHom.ValueGroup₀.embedding γ.1 := by
      obtain ⟨a, ha⟩ :=
        WithZero.ne_zero_iff_exists.mp (MonoidWithZeroHom.ValueGroup₀.embedding_unit_ne_zero γ)
      refine ⟨Multiplicative.toAdd a - 1, ?_⟩
      rw [← ha, show (a : ℤᵐ⁰) = exp (Multiplicative.toAdd a) from rfl]
      exact exp_lt_exp.mpr (by lia)
    refine ⟨(-m).toNat, fun x hx ↦ hts ?_⟩
    refine Set.mem_preimage.mpr (hγ ?_)
    have h1 := v.mem_maximalIdeal_pow_iff (K := K) |>.mp hx
    refine Set.mem_setOf.mpr ((Valuation.restrict_lt_iff_lt_embedding (v := Valued.v)).mpr
      (h1.trans_lt ?_))
    calc exp (-(((-m).toNat : ℤ))) ≤ exp m := exp_le_exp.mpr (by lia)
      _ < _ := hm

instance completeSpace_adicCompletionIntegers : CompleteSpace (v.adicCompletionIntegers K) :=
  (Valued.isClosed_valuationSubring (v.adicCompletion K)).completeSpace_coe

instance isUniformAddGroup_adicCompletionIntegers :
    IsUniformAddGroup (v.adicCompletionIntegers K) :=
  ((Valued.v (R := v.adicCompletion K)).valuationSubring.toSubring.toAddSubgroup).isUniformAddGroup

instance isAdicComplete_adicCompletionIntegers :
    IsAdicComplete (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) :=
  (v.isAdic_maximalIdeal_adicCompletionIntegers (K := K)).isAdicComplete_iff.mpr
    ⟨inferInstance, inferInstance⟩

instance henselianLocalRing_adicCompletionIntegers :
    HenselianLocalRing (v.adicCompletionIntegers K) where
  is_henselian f hf a₀ h₁ h₂ :=
    (IsAdicComplete.henselianRing _
      (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K))).is_henselian f hf a₀ h₁ (h₂.map _)





end IsDedekindDomain.HeightOneSpectrum

end
end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenRealCubicQuotient. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The real-cubic elliptic quotient of the `X₁(18)` sextic

This file records an explicit elliptic quotient of the standard genus-two
model for `X₁(18)`.  Its coefficient field is the totally real cubic field
generated by a root `tau` of

`T³ - 3T - 1`.

Only the algebraic point map is proved here.  In particular, this file makes
no assertion about the Mordell--Weil rank or the rational points of the
elliptic curve.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenRealCubicQuotient

noncomputable section

/-! ## The cubic coefficient field -/























/-- The defining cubic relation in `K`. -/
theorem tau_cubic : tau ^ 3 = 3 * tau + 1 := by
  have h : AdjoinRoot.mk cubicPolynomial cubicPolynomial = 0 :=
    AdjoinRoot.mk_self
  change
    AdjoinRoot.mk cubicPolynomial (X ^ 3 - 3 * X - 1 : Polynomial ℚ) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul,
    map_ofNat, map_one, AdjoinRoot.mk_X] at h
  have h' : tau ^ 3 - 3 * tau - 1 = 0 := by
    simpa only [tau] using h
  linear_combination h'































/-! ## The elliptic quotient and its point map -/





















/-! ## Change to the rational-coefficient model -/











end

end MazurTorsion.XOneEighteenRealCubicQuotient

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionArithmetic. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Exact arithmetic for the `X₁(18)` two-division algebra

This file records the exact algebraic-number certificates used by the
two-descent on the real-cubic elliptic quotient.  The rational cubic

`S³ - 3S - 10`

is proved irreducible by reduction modulo `11`.  We then form its relative
base change to the real cubic field `K = ℚ(τ)`.  All displayed relative
norm identities are checked in the kernel by the resultant formula for a
monogenic cubic algebra.

The relative object is deliberately called an algebra here: its field
structure is supplied only after a separate primitive-element certificate
proves that the two cubic fields are linearly disjoint.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section

namespace Q




theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial :=
  MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial_irreducible
theorem tau_cubic : tau ^ 3 = 3 * tau + 1 :=
  MazurTorsion.XOneEighteenRealCubicQuotient.tau_cubic

end Q



/-! ## The rational two-division cubic -/







































/-! ## The relative cubic algebra over the quotient field -/

























/-! ## Exact relative norm certificates -/

























end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallPrimes. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Small rational primes in the `X₁(18)` two-division compositum

This file gives the tame part of a class-number certificate for the
degree-nine two-division compositum.  For each rational prime between `5`
and `31`, one of the two cubic subfields is inert.  Contraction to that
subfield and multiplicativity of inertia degrees therefore show that every
prime of the compositum above it has inertia degree at least three.

The use of Kummer--Dedekind is unconditional: the two exact rational
power-basis discriminants are first put in the relevant conductors, which
proves that the Kummer--Dedekind exponents are prime to every prime under
consideration.  No maximal-order or class-number computation is assumed.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The two rational cubic power bases -/

theorem coefficientPolynomial_monic : Q.cubicPolynomial.Monic := by
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  monicity <;> norm_num

/-- The rational power basis of the real cubic coefficient field. -/
def _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis : PowerBasis ℚ Q.K :=
  AdjoinRoot.powerBasis' coefficientPolynomial_monic





theorem coefficientPowerBasis_minpolyGen :
    _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.minpolyGen = Q.cubicPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval Q.tau Q.cubicPolynomial = 0 := by
    simp only [Q.cubicPolynomial,
      MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
      map_sub, map_pow, aeval_X, map_mul, map_ofNat, map_one]
    linear_combination Q.tau_cubic
  exact (minpoly.eq_of_irreducible_of_monic Q.cubicPolynomial_irreducible
    hroot coefficientPolynomial_monic).symm













/-! ## Integral generators and their conductors -/











theorem coefficientInteger_minpoly :
    minpoly ℤ coefficientInteger = coefficientPolynomialInt := by
  apply Polynomial.map_injective (algebraMap ℤ ℚ) (algebraMap ℤ ℚ).injective_int
  have hfield := minpoly.isIntegrallyClosed_eq_field_fractions ℚ Q.K
    coefficientInteger.isIntegral
  have hmin := coefficientPowerBasis_minpolyGen
  rw [PowerBasis.minpolyGen_eq] at hmin
  change minpoly ℚ Q.tau = Q.cubicPolynomial at hmin
  rw [← hfield]
  change minpoly ℚ Q.tau = _
  rw [hmin]
  norm_num [coefficientInteger, coefficientPolynomialInt, Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]





















/-! ## Exact finite-field irreducibility certificates -/

















































/-! ## Kummer--Dedekind and inertia in the compositum -/



















end

end MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDyadicCompletionBridge. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The dyadic completion behind the `X₁(18)` local certificate

The finite calculation in `XOneEighteenDyadicLocalImage` takes place in the
unramified cubic ring modulo `2⁷`.  This file begins the arithmetic bridge
to that ring.  It constructs the actual prime above `2` in the full ring of
integers of the real cubic coefficient field and proves, at arbitrary
precision, that quotienting before or after adic completion gives the same
ring.

No conclusion about the local descent image is drawn merely from this
higher-residue comparison.  The remaining bridge must still identify the
chosen polynomial presentation modulo `2⁷`, lift the selected simple root
of the two-division cubic, and treat both integral and nonintegral local
points.
-/

open Polynomial IsDedekindDomain WithZero WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenDyadicCompletionBridge

noncomputable section

open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid
open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionTriadicLift



/-! ## The actual dyadic prime of the coefficient field -/













private instance coefficientPrimeTwoIdeal_liesOver :
    coefficientPrimeTwoIdeal.LiesOver (Ideal.span {(2 : ℤ)}) :=
  coefficientPrimeTwo_mem_primesOver.2



@[simp] theorem coefficientPrimeTwo_asIdeal :
    coefficientPrimeTwo.asIdeal = coefficientPrimeTwoIdeal :=
  rfl

theorem coefficientPrimeTwoIdeal_eq_span :
    coefficientPrimeTwoIdeal = Ideal.span {(2 : 𝓞 Q.K)} := by
  rw [coefficientPrimeTwoIdeal]
  rw [NumberField.Ideal.primesOverSpanEquivMonicFactorsMod_symm_apply_eq_span
    coefficient_not_dvd_exponent_two
    coefficientPolynomialInt_mem_monicFactors_two]
  have hzero : Polynomial.aeval coefficientInteger
      coefficientPolynomialInt = 0 := by
    rw [← coefficientInteger_minpoly]
    exact minpoly.aeval ℤ coefficientInteger
  rw [hzero]
  simp

@[simp] theorem coefficientPrimeTwo_span :
    coefficientPrimeTwo.asIdeal = Ideal.span {(2 : 𝓞 Q.K)} := by
  rw [coefficientPrimeTwo_asIdeal, coefficientPrimeTwoIdeal_eq_span]

/-! ## Quotients commute with adic completion -/

section CompletionQuotient

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]











end CompletionQuotient

/-! ## The coefficient completion modulo `2⁷` -/

open MazurTorsion.XOneEighteenDyadicLocalImage























































/-! ## The selected simple root of the local two-division cubic -/





private theorem localTwoDivisionPolynomial_monic :
    localTwoDivisionPolynomial.Monic := by
  simp only [localTwoDivisionPolynomial]
  monicity <;> norm_num

private theorem ten_mem_coefficientPrimeTwo :
    (10 : 𝓞 Q.K) ∈ coefficientPrimeTwo.asIdeal := by
  rw [coefficientPrimeTwo_span, Ideal.mem_span_singleton]
  exact ⟨5, by norm_num⟩

private theorem three_not_mem_coefficientPrimeTwo :
    (3 : 𝓞 Q.K) ∉ coefficientPrimeTwo.asIdeal := by
  intro hthree
  have hthree' : algebraMap ℤ (𝓞 Q.K) (3 : ℤ) ∈
      coefficientPrimeTwoIdeal := by
    simpa only [coefficientPrimeTwo_asIdeal, map_ofNat] using hthree
  have hz : (3 : ℤ) ∈ Ideal.span {(2 : ℤ)} := by
    exact (Ideal.mem_of_liesOver (P := coefficientPrimeTwoIdeal)
      (p := Ideal.span {(2 : ℤ)}) 3).2 hthree'
  rw [Ideal.mem_span_singleton] at hz
  obtain ⟨a, ha⟩ := hz
  omega

private theorem ten_mem_completionMaximalIdeal :
    (10 : CoefficientCompletionIntegers) ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  have h := (coefficientPrimeTwo.algebraMap_mem_maximalIdeal_pow_iff
    (K := Q.K) (r := (10 : 𝓞 Q.K)) (n := 1)).2 (by
      simpa only [pow_one] using ten_mem_coefficientPrimeTwo)
  simpa only [pow_one, map_ofNat] using h

private theorem three_not_mem_completionMaximalIdeal :
    (3 : CoefficientCompletionIntegers) ∉
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  intro hthree
  have h := (coefficientPrimeTwo.algebraMap_mem_maximalIdeal_pow_iff
    (K := Q.K) (r := (3 : 𝓞 Q.K)) (n := 1)).1 (by
      simpa only [pow_one, map_ofNat] using hthree)
  exact three_not_mem_coefficientPrimeTwo (by
    simpa only [pow_one] using h)

private theorem exists_localTwoDivisionRoot_aux :
    ∃ sHat : CoefficientCompletionIntegers,
      localTwoDivisionPolynomial.IsRoot sHat ∧
        sHat ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  have hvalue : localTwoDivisionPolynomial.eval 0 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
    have heval : localTwoDivisionPolynomial.eval 0 =
        (-10 : CoefficientCompletionIntegers) := by
      norm_num [localTwoDivisionPolynomial]
    rw [heval]
    exact (IsLocalRing.maximalIdeal CoefficientCompletionIntegers).neg_mem
      ten_mem_completionMaximalIdeal
  have hderivative :
      IsUnit (localTwoDivisionPolynomial.derivative.eval 0) := by
    have hthreeUnit : IsUnit (3 : CoefficientCompletionIntegers) :=
      IsLocalRing.notMem_maximalIdeal.mp
        three_not_mem_completionMaximalIdeal
    have hderiv : localTwoDivisionPolynomial.derivative.eval 0 =
        (-3 : CoefficientCompletionIntegers) := by
      norm_num [localTwoDivisionPolynomial]
    rw [hderiv]
    exact hthreeUnit.neg
  obtain ⟨sHat, hsHat, hsHatmem⟩ :=
    HenselianLocalRing.is_henselian localTwoDivisionPolynomial
      localTwoDivisionPolynomial_monic 0 hvalue hderivative
  exact ⟨sHat, hsHat, by simpa only [sub_zero] using hsHatmem⟩





















/-! ## The unramified dyadic uniformizer and square lifting -/













/-! ## The normalized projected curve over the integer ring -/



























/-! ## Passage to the completion field -/























/-! ## Projection of the genuine relative descent algebra -/























/-! ## The selected factor of the base-changed minimal descent algebra -/











/-! ## The local image of the minimal descent map -/







































end

end MazurTorsion.XOneEighteenDyadicCompletionBridge

end

open MazurTorsion.XOneEighteenDyadicCompletionBridge

theorem solution :
    ∃ r : CoefficientCompletionIntegers,
      localTwoDivisionPolynomial.IsRoot r ∧
        r ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  exact exists_localTwoDivisionRoot_aux

#print axioms solution
