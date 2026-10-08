-- Prove2me | solution 1 for MazurTransfer.order18_selected_local_kernel_representative_separation
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T18:14:10.166472+00:00
-- url     : https://prove2.me/submissions/ed818dae-ac7b-41de-8c72-cc9ff4d4d5b2

import Mathlib
import Definitions.Def_MazurTransfer_Order18SelectedLocalProjectionData
import Theorems.Thm_MazurTransfer_order18_coefficient_dyadic_prime_certificate
import Theorems.Thm_MazurTransfer_order18_coefficient_hensel_root_exists
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

namespace MazurTorsion.XOneEighteenGlobalKernelEquivalence
end MazurTorsion.XOneEighteenGlobalKernelEquivalence

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

namespace MazurTorsion.XOneEighteenDyadicCompletionBridge
private theorem exists_localTwoDivisionRoot_aux :
    ∃ r : CoefficientCompletionIntegers,
      localTwoDivisionPolynomial.IsRoot r ∧
        r ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers :=
  MazurTransfer.order18_coefficient_hensel_root_exists
end MazurTorsion.XOneEighteenDyadicCompletionBridge


/- Source module: EllipticCurves.Mathlib.Basic. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Material for Mathlib

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

This file collects the general-purpose results developed for `EllipticCurves.WeakMordellWeil`
that have nothing to do with elliptic curves and look like candidates for Mathlib.

* `MonoidHom.ofMapMulMulEqOne`: build a `MonoidHom` from `f 1 = 1` and
  `a * b * c = 1 → f a * f b * f c = 1`.
* `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`: dominance of the
  leading term of a monic polynomial with integral coefficients, and integrality of its roots.
  `Valuation.eq_one_of_mul_eq_one`: a factor of a unit is a unit, provided both factors are
  integral.
* `IsDedekindDomain.HeightOneSpectrum.finite_setOf_valuation_ne_one`,
  `.below` (the prime lying below a prime of an integral extension), `.primesAbove` and its
  finiteness `.primesAbove_finite`,
  `IsDedekindDomain.selmerGroupAbove`, `.valuationOfNeZero_eq_iff`,
  `.dvd_toAdd_valuationOfNeZero` and
  `.valuationOfNeZeroMod_mk_eq_one_iff`, which turns the Selmer condition into a
  divisibility of valuations; `Set.integer_mono` and `Set.unit_mono`, monotonicity of the
  `S`-integers and `S`-units in `S`. (`Mathlib.RingTheory.DedekindDomain.SelmerGroup` has a
  `TODO` about the `Multiplicative`/`Additive` defeq abuse in `valuationOfNeZeroMod`
  and provides no API for it.)
* `Units.modPow`, the group of `n`-th power classes of units, which
  `Mathlib.RingTheory.DedekindDomain.SelmerGroup` has only as a local notation, together
  with `map`, `congr` and `piEquiv`.
* Division with remainder by a monic polynomial: `Polynomial.Monic.divByMonic_mul_add`,
  `.modByMonic_mul_add`, `modByMonic_mem_degreeLT`, `divByMonic_mem_degreeLT`.
* `isIntegralClosure_int_integralClosure`, `NumberField.finite_classGroup_integralClosure` and
  `NumberField.fg_units_integralClosure`: the class number theorem and the finite generation of
  the unit group for the integral closure of `𝓞 K` in a finite extension of a number field `K`;
  `NumberField.subsingleton_classGroup_integralClosure` and
  `NumberField.finrank_additive_units_integralClosure` transport triviality of the class
  group and the unit rank from `𝓞 L`.
* `AdjoinRoot.discr_powerBasis_eq_discr`, `NumberField.exists_eq_discr_mul_sq`,
  `RingOfIntegers.isPrincipalIdealRing_of_finrank_eq_three_of_abs_discr_le` and
  `RingOfIntegers.finrank_additive_units_of_discr_neg`/`_pos`: the discriminant of the power
  basis of `K[X]/(f)` is `f.discr`; the field discriminant is any integral power-basis
  discriminant divided by a square; a cubic field with `|discr| ≤ 49` has trivial class group
  (Minkowski bound), and the sign of its discriminant determines the unit rank (Dirichlet).
* `AdjoinRoot.norm_mk_eq_resultant`: for monic `g`, the norm of `AdjoinRoot.mk g p` is the
  resultant of `g` and `p`. This links `Polynomial.resultant` to `Algebra.norm`.
* `AdjoinRoot.equivPiFactors`: for nonzero squarefree `f`, `K[X]/(f)` is the product of the
  fields `K[X]/(p)` over the monic irreducible factors `p` of `f`, and the induced
  `AdjoinRoot.modPowEquivPiFactors` on `n`-th power classes of units.
* `Polynomial.discr_X_sub_C_mul`: splitting off a linear factor multiplies the discriminant
  by the square of the evaluation, `((X - C x) * g).discr = g.discr * g.eval x ^ 2`.
* `Matrix.det_blockDiagonal'`, `LinearMap.det_pi'`, `Algebra.norm_prod`, `Algebra.norm_pi`:
  determinants and norms on (dependent) products decompose as products; together with
  `AdjoinRoot.norm_eq_prod_norm_projFactor`, the norm on `K[X]/(f)` as the product of the
  norms on the field factors.
* General helpers extracted from the rank example: `Squarefree.map` (transport along a
  `MulEquiv`), `Polynomial.Monic.irreducible_map_fraction_map_of_irreducible_map`
  (irreducibility over the fraction field via reduction modulo a prime),
  `Polynomial.Factors.coe_eq`, `AdjoinRoot.isIntegralElem_root_of_map`,
  `AdjoinRoot.finrank_eq_natDegree`, and the `IsPrincipalIdealRing (𝓞 ℚ)` instance.
-/

section

section Group

variable {G H : Type*} [Group G] [Group H]









end Group

section Units

variable {α : Type*} [Monoid α]





end Units

section modPow







namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

open QuotientGroup





lemma mk_eq_one_iff {u : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = 1 ↔ ∃ w : αˣ, w ^ n = u := by
  simp



/-- The class of a unit is trivial in `Units.modPow α 2` exactly when the unit is a square
in `α`. -/
lemma mk_eq_one_iff_isSquare {u : αˣ} :
    (QuotientGroup.mk u : Units.modPow α 2) = 1 ↔ IsSquare (u : α) := by
  rw [mk_eq_one_iff]
  refine ⟨fun ⟨w, hw⟩ ↦ ⟨w, by rw [← hw]; push_cast [sq]; rfl⟩, fun ⟨s, hs⟩ ↦ ?_⟩
  have hsu : IsUnit s := isUnit_of_mul_isUnit_left (hs ▸ u.isUnit)
  exact ⟨hsu.unit, Units.ext (by rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, sq, ← hs])⟩









@[simp]
lemma map_mk (φ : α →* β) (n : ℕ) (u : αˣ) :
    map φ n (QuotientGroup.mk u) = QuotientGroup.mk (Units.map φ u) :=
  rfl

















end Units.modPow

end modPow

section Ideal



end Ideal

section LinearAlgebra







end LinearAlgebra

section Valuation

open Polynomial

variable {L Γ : Type*} [CommRing L] [LinearOrderedCommGroupWithZero Γ] (ν : Valuation L Γ)
  {t a b : L}









end Valuation

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]























variable (R) (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra R B]



-- The `IsDedekindDomain` instances are needed to *state* this (they are parameters of
-- `HeightOneSpectrum`), but are erased from the proof term (`nolint unusedArguments`),
-- which makes the linter fire spuriously.


-- as for `primesAbove_mono`, the `IsDedekindDomain` instances are needed for the statement
















-- as for `mem_selmerGroupAbove_iff`, the instances are needed for the statement only


namespace IsDiscreteValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]



variable {A}



end IsDiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]



-- the `IsDedekindDomain` instances are needed to state this, but the proof (`rfl`) erases them


variable {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]







end IsDedekindDomain.HeightOneSpectrum

end DedekindDomain

namespace Polynomial

variable {R : Type*} [CommRing R] {g : R[X]}



















section

variable [Nontrivial R] {q : R[X]} {n : ℕ}















end

section Sylvester

open Module LinearMap LinearEquiv

variable [Nontrivial R] {p : R[X]} {n : ℕ}

/-!
### The norm on `AdjoinRoot g` is the resultant

Write `m = g.natDegree` and `n = p.natDegree`. The Sylvester map
`S : R[X]_m × R[X]_n →ₗ R[X]_(m+n)`, `(u, v) ↦ g * v + p * u`, has the Sylvester matrix as its
matrix, so `det S = resultant g p m n`.

Taking `p = 1` gives a map `Ψ : (u, v) ↦ g * v + u`, which is a linear *equivalence* when `g` is
monic (its inverse is `q ↦ (q %ₘ g, q /ₘ g)`), and `det Ψ = resultant g 1 m n = 1`.

Now `S = Ψ ∘ₗ B` where `B := Ψ⁻¹ ∘ₗ S` is the endomorphism
`(u, v) ↦ ((p * u) %ₘ g, v + (p * u) /ₘ g)` of `R[X]_m × R[X]_n`, by `modByMonic_add_div`.
In the block decomposition the matrix of `B` is lower triangular with diagonal blocks
`mulModByMonic hg p` and `1`, so `det B = det (mulModByMonic hg p)`.

Finally `mk g : R[X]_m ≃ₗ AdjoinRoot g` conjugates `mulModByMonic hg p` into multiplication by
`mk g p`, whose determinant is by definition `Algebra.norm R (mk g p)`.

No signs appear anywhere: `B` is an endomorphism, so the two blocks are never reordered.
-/



















end Sylvester



end Polynomial

open Polynomial LinearMap LinearEquiv

namespace AdjoinRoot

variable {R : Type*} [CommRing R] {g : R[X]} {n : ℕ}



















section Map

variable {S : Type*} [CommRing S] (σ : R →+* S)



end Map

end AdjoinRoot



/-! ### The norm on a product algebra -/





section EtaleDecomposition

/-!
### Decomposition of `K[X]/(f)` into a product of fields

For a nonzero squarefree `f` over a field `K`, the étale algebra `AdjoinRoot f` is the product
of the fields `AdjoinRoot p`, where `p` runs over the distinct irreducible factors of `f`.
This is what lets one talk about the primes, and hence the Selmer group, of `AdjoinRoot f`:
they are those of the factors.

If moreover `f` is separable, each factor is separable, so each `AdjoinRoot p` is a finite
separable extension of `K` and its integral closure over a Dedekind domain is again Dedekind.
-/

open Polynomial UniqueFactorizationMonoid

namespace Polynomial

variable {K : Type*} [Field K] {f : K[X]}



namespace Factors





































end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}



































end AdjoinRoot

end EtaleDecomposition

/-!
### Rings of integers in finite extensions of number fields

The integral closure of `𝓞 K` in a finite extension `L` of a number field `K` is (isomorphic to)
the ring of integers of `L`; consequently the class number theorem and (the finite-generation
part of) Dirichlet's unit theorem apply to it.
-/

section NumberField

open NumberField

variable (K L : Type*) [Field K] [Field L] [Algebra K L]





variable [NumberField K] [FiniteDimensional K L]









end NumberField

/-!
### Discriminants, class numbers, and unit ranks of cubic fields

The discriminant of a number field is the discriminant of any power basis with integral
generator divided by a square; consequently a cubic field whose power-basis discriminant is
at most `49` in absolute value has trivial class group (by the Minkowski bound), and the sign
of the power-basis discriminant determines the signature and hence, by Dirichlet's unit
theorem, the unit rank (`1` if negative, `2` if positive).
-/

section Discriminant

open NumberField Module

variable {K : Type*} [Field K] [NumberField K]









end Discriminant

end

end


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

















end IsDedekindDomain.HeightOneSpectrum

end
end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDyadicGeneratorCertificate. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Dyadic reductions of the four `X₁(18)` norm-kernel generators

At the dyadic factor with `s ≡ 74`, the normalized degree-nine generator
reduces to `7 + 10τ + τ²` modulo `16`.  This file evaluates the four integral
generator polynomials at that element and checks that their fifteen nonempty
products are precisely the nonsquare triples certified in
`XOneEighteenDyadicCubicCertificate`.

The separate integral-reduction bridge must prove that the global algebraic
integers reduce to these triples.  No completion or integrality assertion is
made here.
-/

namespace MazurTorsion.XOneEighteenDyadicGeneratorCertificate

open MazurTorsion.XOneEighteenDyadicCubicCertificate



/-- Powers for the cubic multiplication, rather than the pointwise
multiplication inherited by coefficient vectors. -/
def cubicPow (x : CubicResidue) : ℕ → CubicResidue
  | 0 => one
  | n + 1 => mul (cubicPow x n) x



/-- Reduction of the first integral norm-kernel generator polynomial. -/
def firstGenerator : CubicResidue :=
  -cubicPow normalizedGenerator 8 + 3 * cubicPow normalizedGenerator 7 -
    8 * cubicPow normalizedGenerator 5 + 6 * cubicPow normalizedGenerator 4 +
    8 * cubicPow normalizedGenerator 3 - 7 * cubicPow normalizedGenerator 2 -
    3 * normalizedGenerator + 3 * one

/-- Reduction of the second integral norm-kernel generator polynomial. -/
def secondGenerator : CubicResidue :=
  -cubicPow normalizedGenerator 6 + 3 * cubicPow normalizedGenerator 5 -
    cubicPow normalizedGenerator 4 - 4 * cubicPow normalizedGenerator 3 +
    3 * cubicPow normalizedGenerator 2 + 3 * normalizedGenerator - one

/-- Reduction of the third integral norm-kernel generator polynomial. -/
def thirdGenerator : CubicResidue :=
  -mul
    (cubicPow normalizedGenerator 3 - cubicPow normalizedGenerator 2 + one)
    (cubicPow normalizedGenerator 5 - 3 * cubicPow normalizedGenerator 4 +
      cubicPow normalizedGenerator 3 + 4 * cubicPow normalizedGenerator 2 -
      3 * normalizedGenerator - 4 * one)

/-- Reduction of the fourth integral norm-kernel generator polynomial. -/
def fourthGenerator : CubicResidue :=
  -mul
    (cubicPow normalizedGenerator 3 - 2 * cubicPow normalizedGenerator 2 +
      normalizedGenerator + one)
    (cubicPow normalizedGenerator 3 - cubicPow normalizedGenerator 2 -
      2 * normalizedGenerator - one)

/-- The four reductions, in the order used by binary masks. -/
def generator : Fin 4 → CubicResidue :=
  ![firstGenerator, secondGenerator, thirdGenerator, fourthGenerator]

/-- Exact reductions of the four generator polynomials. -/
theorem generator_eq :
    generator = ![![15, 1, 5], ![12, 11, 11], ![14, 6, 2], ![2, 0, 2]] := by
  decide +kernel

/-- Product of the four generators selected by the low four bits of a mask. -/
def maskedProduct (mask : Fin 16) : CubicResidue :=
  mul (if mask.val.testBit 0 then generator 0 else one) <|
    mul (if mask.val.testBit 1 then generator 1 else one) <|
      mul (if mask.val.testBit 2 then generator 2 else one)
        (if mask.val.testBit 3 then generator 3 else one)

/-- The canonical nonzero four-bit mask corresponding to `i+1`. -/
def nonzeroMask (i : Fin 15) : Fin 16 :=
  ⟨i.val + 1, by omega⟩

/-- The fifteen nonempty products agree with the certified candidate table. -/
theorem maskedProduct_nonzeroMask (i : Fin 15) :
    maskedProduct (nonzeroMask i) = candidate i := by
  decide +kernel +revert

/-- Every nonempty product of the four projected generators is a nonsquare
modulo `16`. -/
theorem maskedProduct_nonsquare (i : Fin 15) :
    ¬ XOneEighteenDyadicCubicCertificate.IsSquare
      (maskedProduct (nonzeroMask i)) := by
  rw [maskedProduct_nonzeroMask]
  exact candidate_nonsquare i

end MazurTorsion.XOneEighteenDyadicGeneratorCertificate

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



theorem relativePolynomial_monic : relativePolynomial.Monic := by
  simp only [relativePolynomial]
  monicity <;> norm_num

theorem relativePolynomial_natDegree : relativePolynomial.natDegree = 3 := by
  simp only [relativePolynomial]
  compute_degree!









/-- The coefficient-field relation remains exact after base change. -/
theorem t_cubic : t ^ 3 = 3 * t + 1 := by
  simpa only [t, map_pow, map_mul, map_ofNat, map_add, map_one] using
    congrArg (algebraMap Q.K M) Q.tau_cubic

/-- The defining relation in the relative cubic algebra. -/
theorem s_cubic : s ^ 3 = 3 * s + 10 := by
  have h : AdjoinRoot.mk relativePolynomial relativePolynomial = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk relativePolynomial
    (X ^ 3 - 3 * X - 10 : Polynomial Q.K) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul, map_ofNat, map_ofNat,
    AdjoinRoot.mk_X] at h
  have h' : s ^ 3 - 3 * s - 10 = 0 := by
    simpa only [s] using h
  linear_combination h'

/-- The relative cubic algebra has the expected rank `3` over `K`, without
using irreducibility. -/
theorem finrank_M_over_K : Module.finrank Q.K M = 3 := by
  rw [(AdjoinRoot.powerBasis' relativePolynomial_monic).finrank]
  exact relativePolynomial_natDegree





/-! ## Exact relative norm certificates -/



theorem quadraticElement_eq (a b c : Q.K) :
    quadraticElement a b c =
      algebraMap Q.K M a * s ^ 2 + algebraMap Q.K M b * s +
        algebraMap Q.K M c := by
  simp [quadraticElement, s]





















end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionNorms. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Concrete norm certificates for the `X₁(18)` two-division algebra

This file evaluates the relative norms of the explicit squareclass
representatives used in the two-descent.  The proofs use only the determinant
formula from `XOneEighteenTwoDivisionArithmetic` and the defining cubic
relation for the coefficient generator.  In particular, no field structure on
the relative cubic algebra is used.
-/

namespace MazurTorsion.XOneEighteenTwoDivisionArithmetic

noncomputable section



























end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDyadicLocalImage. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The cubic dyadic local image for the `X₁(18)` quotient

This file models the unramified cubic quotient modulo `2⁷` as

`(ZMod 128)[T] / (T³ - 3T - 1)`.

The normalized local curve has equation

`Y² = X (X² + 62X + 65)`.

Its quadratic factor is exactly `(X + 31)²` modulo `128`.  The proof
below uses that factorization together with a bounded dyadic valuation
argument; it does not enumerate pairs of cubic residues.
-/

open Polynomial

namespace MazurTorsion.XOneEighteenDyadicLocalImage

noncomputable section

/-- The coefficient cubic at dyadic precision `2⁷`. -/
def cubicPolynomial128 : Polynomial (ZMod 128) :=
  X ^ 3 - 3 * X - 1

/-- The unramified cubic residue ring modulo `2⁷`. -/
abbrev CubicResidue128 := AdjoinRoot cubicPolynomial128























































































end

end MazurTorsion.XOneEighteenDyadicLocalImage

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionClassNumber. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Integral arithmetic for the `X₁(18)` two-division compositum

This file begins the independently checked class-number certificate for the
degree-nine two-division compositum.  The first essential step is to prove
that the relative cubic algebra from
`XOneEighteenTwoDivisionArithmetic` really is a field.  We do this without a
computer algebra oracle: if the two rational cubic fields met, their power
bases would be related by a rational change-of-basis matrix.  Their exact
discriminants have opposite signs, which is impossible because a basis
discriminant changes by the square of a determinant.
-/

open Polynomial Module
open scoped Matrix

namespace MazurTorsion.XOneEighteenTwoDivisionClassNumber

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic

private theorem coefficientPolynomial_monic : Q.cubicPolynomial.Monic := by
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  monicity <;> norm_num

private def coefficientPowerBasis : PowerBasis ℚ Q.K :=
  AdjoinRoot.powerBasis' coefficientPolynomial_monic









private theorem coefficientPowerBasis_dim : coefficientPowerBasis.dim = 3 := by
  rw [coefficientPowerBasis, AdjoinRoot.powerBasis'_dim]
  simp only [MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  compute_degree!



/-! ## The two incompatible cubic discriminants -/







/-! ## Linear disjointness of the two rational cubic fields -/

private theorem coefficientField_finrank : Module.finrank ℚ Q.K = 3 := by
  rw [coefficientPowerBasis.finrank, coefficientPowerBasis_dim]









/-- The compositum has degree nine over `ℚ`. -/
theorem finrank_M_over_rat : Module.finrank ℚ M = 9 := by
  rw [← Module.finrank_mul_finrank ℚ Q.K M, finrank_M_over_K,
    coefficientField_finrank]

end

end MazurTorsion.XOneEighteenTwoDivisionClassNumber

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



theorem _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim : _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.dim = 3 := by
  rw [_root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis, AdjoinRoot.powerBasis'_dim]
  simp only [MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  compute_degree!



private theorem norm_cubic_derivative
    {L : Type*} [CommRing L] [Algebra ℚ L]
    (pb : PowerBasis ℚ L) (hdim : pb.dim = 3) (d : ℚ)
    (hmin : pb.minpolyGen = X ^ 3 - 3 * X - C d) :
    Algebra.norm ℚ (3 * pb.gen ^ 2 - 3) = 27 * (d ^ 2 - 4) := by
  rw [Algebra.norm_eq_matrix_det pb.basis]
  simp only [map_sub, map_mul, map_pow, map_ofNat]
  rw [pb.leftMulMatrix, hmin]
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let companion : Matrix (Fin pb.dim) (Fin pb.dim) ℚ :=
    fun i j ↦ if (j : ℕ) + 1 = pb.dim then
      -(X ^ 3 - 3 * X - C d).coeff i
    else if (i : ℕ) = j + 1 then 1 else 0
  change Matrix.det
    (algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3 *
        companion ^ 2 -
      algebraMap ℚ (Matrix (Fin pb.dim) (Fin pb.dim) ℚ) 3) = _
  have hcompanion :
      Matrix.reindexAlgEquiv ℚ ℚ e companion =
        !![0, 0, d; 1, 0, 3; 0, 1, 0] := by
    ext i j
    change companion (e.symm i) (e.symm j) = _
    fin_cases i <;> fin_cases j <;>
      simp [companion, e, hdim, coeff_sub, coeff_X_pow, coeff_X]
  conv_lhs => rw [← Matrix.det_reindexAlgEquiv ℚ (R := ℚ) e]
  rw [map_sub, map_mul, map_pow]
  rw [(Matrix.reindexAlgEquiv ℚ ℚ e).commutes 3, hcompanion]
  rw [Matrix.det_fin_three]
  simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, pow_two]
  ring

/-- The exact rational power-basis discriminant of the coefficient cubic. -/
theorem coefficientPowerBasis_discriminant :
    Algebra.discr ℚ _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.basis = 81 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [_root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank, _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, coefficientPowerBasis_minpolyGen]
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
    derivative_sub, derivative_pow, derivative_X, derivative_mul,
    derivative_ofNat, derivative_one, mul_one, Nat.cast_ofNat,
    zero_mul, sub_zero]
  rw [show _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.gen = Q.tau by rfl]
  have hnorm := norm_cubic_derivative _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis
    _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim 1 (by
      simpa only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
        C_1] using coefficientPowerBasis_minpolyGen)
  rw [show _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.gen = Q.tau by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]
  norm_num



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













private theorem integer_discriminant_mem_conductor
    {L : Type*} [Field L] [NumberField L]
    (B : PowerBasis ℚ L) (theta : 𝓞 L)
    (hgen : B.gen = (theta : L)) (d : ℤ)
    (hdisc : Algebra.discr ℚ B.basis = (d : ℚ)) :
    (d : 𝓞 L) ∈ conductor ℤ theta := by
  have hfield :
      algebraMap (𝓞 L) L (d : 𝓞 L) ∈
        IsLocalization.coeSubmodule L (conductor ℤ theta) := by
    rw [mem_coeSubmodule_conductor]
    intro z
    have hz := Algebra.discr_mul_isIntegral_mem_adjoin ℚ
      (B := B) (by simpa only [hgen] using theta.isIntegral_coe)
      z.isIntegral_coe
    rw [hdisc] at hz
    simpa only [RingOfIntegers.coe_eq_algebraMap, map_intCast,
      hgen, Algebra.smul_def, IsScalarTower.algebraMap_apply ℤ ℚ L] using hz
  obtain ⟨z, hz, hzmap⟩ :=
    (IsLocalization.mem_coeSubmodule L (conductor ℤ theta)).mp hfield
  have hz' : z = (d : 𝓞 L) := RingOfIntegers.coe_injective hzmap
  simpa only [hz'] using hz

/-- The integer `81` lies in the conductor of `ℤ[τ]` in the coefficient
field's full ring of integers. -/
theorem coefficient_discriminant_mem_conductor :
    (81 : 𝓞 Q.K) ∈ conductor ℤ coefficientInteger := by
  apply integer_discriminant_mem_conductor _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis
    coefficientInteger (by rfl) 81
  exact coefficientPowerBasis_discriminant





/-! ## Exact finite-field irreducibility certificates -/

















































/-! ## Kummer--Dedekind and inertia in the compositum -/



















end

end MazurTorsion.XOneEighteenTwoDivisionSmallPrimes

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionPrimitive. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# A primitive element for the `X₁(18)` two-division compositum

This file gives a kernel-checked monogenic presentation of the degree-nine
two-division compositum.  The chosen generator is the simple difference
`u = t - s` of the two cubic generators.  Its polynomial is obtained by a
bounded resultant computation, but both the root identity and the inverse
formula recovering `t` are verified directly from the two cubic relations.

No assertion is made here about the ring of integers, an integral basis, or
the field discriminant.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenTwoDivisionPrimitive

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber

/-- A primitive-element candidate for the degree-nine compositum. -/
def primitiveElement : M := t - s

/-- The exact resultant polynomial of `t - s`. -/
def primitivePolynomial : Polynomial ℚ :=
  X ^ 9 - 18 * X ^ 7 + 27 * X ^ 6 + 81 * X ^ 5 -
    81 * X ^ 4 + 405 * X ^ 3 + 729 * X + 729

theorem primitivePolynomial_monic : primitivePolynomial.Monic := by
  simp only [primitivePolynomial]
  monicity <;> norm_num

theorem primitivePolynomial_natDegree :
    primitivePolynomial.natDegree = 9 := by
  simp only [primitivePolynomial]
  compute_degree!

/-- Direct verification of the bounded resultant identity. -/
theorem primitiveElement_root :
    Polynomial.aeval primitiveElement primitivePolynomial = 0 := by
  simp only [primitiveElement, primitivePolynomial, map_add, map_sub,
    map_mul, map_pow, map_ofNat, aeval_X]
  linear_combination
    (84 * s ^ 6 - 126 * s ^ 5 * t + 126 * s ^ 4 * t ^ 2 -
      252 * s ^ 4 - 84 * s ^ 3 * t ^ 3 + 378 * s ^ 3 * t -
      624 * s ^ 3 + 36 * s ^ 2 * t ^ 4 - 270 * s ^ 2 * t ^ 2 +
      441 * s ^ 2 * t - 9 * s * t ^ 5 + 99 * s * t ^ 3 -
      171 * s * t ^ 2 - 108 * s * t - 90 * s + t ^ 6 -
      15 * t ^ 4 + 28 * t ^ 3 + 36 * t ^ 2 - 12 * t + 541) *
        t_cubic +
    (-s ^ 6 + 9 * s ^ 5 * t - 36 * s ^ 4 * t ^ 2 + 15 * s ^ 4 +
      153 * s ^ 3 * t + 101 * s ^ 3 - 108 * s ^ 2 * t ^ 2 -
      198 * s ^ 2 * t - 36 * s ^ 2 + 171 * s * t ^ 2 +
      108 * s * t + 120 * s - 234 * t - 127) * s_cubic

/-- A rational polynomial which recovers the coefficient-field generator
`t` from the primitive element. -/
def coefficientGeneratorPolynomial : Polynomial ℚ :=
  C (1 / 2673) *
    (1944 - 1944 * X + 2511 * X ^ 2 - 810 * X ^ 3 +
      135 * X ^ 4 + 216 * X ^ 5 - 72 * X ^ 6 - 6 * X ^ 7 +
      4 * X ^ 8)

/-- Direct verification of the inverse elimination identity. -/
theorem coefficientGenerator_reconstruction :
    Polynomial.aeval primitiveElement coefficientGeneratorPolynomial = t := by
  simp only [primitiveElement, coefficientGeneratorPolynomial, map_mul,
    aeval_C, map_add, map_sub, map_pow, map_ofNat, aeval_X]
  rw [map_div₀, map_one, map_ofNat]
  have helim :
      2673 * t -
        (1944 - 1944 * (t - s) + 2511 * (t - s) ^ 2 -
          810 * (t - s) ^ 3 + 135 * (t - s) ^ 4 +
          216 * (t - s) ^ 5 - 72 * (t - s) ^ 6 -
          6 * (t - s) ^ 7 + 4 * (t - s) ^ 8) = 0 := by
    linear_combination
      (224 * s ^ 5 - 280 * s ^ 4 * t + 210 * s ^ 4 +
        224 * s ^ 3 * t ^ 2 - 210 * s ^ 3 * t - 768 * s ^ 3 -
        112 * s ^ 2 * t ^ 3 + 126 * s ^ 2 * t ^ 2 +
        744 * s ^ 2 * t - 1894 * s ^ 2 + 32 * s * t ^ 4 -
        42 * s * t ^ 3 - 336 * s * t ^ 2 + 986 * s * t -
        510 * s - 4 * t ^ 5 + 6 * t ^ 4 + 60 * t ^ 3 -
        202 * t ^ 2 + 51 * t + 264) * t_cubic +
      (-4 * s ^ 5 + 32 * s ^ 4 * t - 6 * s ^ 4 -
        112 * s ^ 3 * t ^ 2 + 42 * s ^ 3 * t + 60 * s ^ 3 -
        126 * s ^ 2 * t ^ 2 + 336 * s ^ 2 * t + 382 * s ^ 2 -
        96 * s * t ^ 2 - 284 * s * t + 195 * s +
        256 * t ^ 2 - 546 * t + 168) * s_cubic
  linear_combination (-1 / 2673 : ℚ) * helim

theorem coefficientGenerator_mem_adjoin :
    t ∈ Algebra.adjoin ℚ ({primitiveElement} : Set M) := by
  rw [← coefficientGenerator_reconstruction]
  exact Polynomial.aeval_mem_adjoin_singleton ℚ primitiveElement

theorem relativeGenerator_mem_adjoin :
    s ∈ Algebra.adjoin ℚ ({primitiveElement} : Set M) := by
  have hu : primitiveElement ∈
      Algebra.adjoin ℚ ({primitiveElement} : Set M) :=
    Algebra.self_mem_adjoin_singleton ℚ primitiveElement
  have hsub := (Algebra.adjoin ℚ ({primitiveElement} : Set M)).sub_mem
    coefficientGenerator_mem_adjoin hu
  simpa only [primitiveElement, sub_sub_cancel] using hsub

/-- The single element `t - s` generates the entire compositum over `ℚ`. -/
theorem primitiveElement_adjoin_eq_top :
    Algebra.adjoin ℚ ({primitiveElement} : Set M) = ⊤ := by
  let A : Subalgebra ℚ M :=
    Algebra.adjoin ℚ ({primitiveElement} : Set M)
  have ht : t ∈ A := coefficientGenerator_mem_adjoin
  have hs : s ∈ A := relativeGenerator_mem_adjoin
  have hcoeff : ∀ a : Q.K, algebraMap Q.K M a ∈ A := by
    intro a
    induction a using AdjoinRoot.induction_on with
    | ih q =>
        induction q using Polynomial.induction_on with
        | C r =>
            simp only [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq]
            change algebraMap Q.K M (algebraMap ℚ Q.K r) ∈ A
            rw [← IsScalarTower.algebraMap_apply ℚ Q.K M]
            exact A.algebraMap_mem r
        | add p q hp hq =>
            simpa only [map_add] using A.add_mem hp hq
        | monomial n r hr =>
            simp only [map_mul, map_pow, AdjoinRoot.mk_C,
              AdjoinRoot.mk_X, ← AdjoinRoot.algebraMap_eq]
            change algebraMap Q.K M (algebraMap ℚ Q.K r) *
              t ^ (n + 1) ∈ A
            rw [← IsScalarTower.algebraMap_apply ℚ Q.K M]
            exact A.mul_mem (A.algebraMap_mem r) (A.pow_mem ht (n + 1))
  have hpolynomial : ∀ p : Polynomial Q.K,
      AdjoinRoot.mk relativePolynomial p ∈ A := by
    intro p
    induction p using Polynomial.induction_on with
    | C a =>
        simpa only [AdjoinRoot.mk_C, ← AdjoinRoot.algebraMap_eq] using
          hcoeff a
    | add p q hp hq =>
        simpa only [map_add] using A.add_mem hp hq
    | monomial n a ha =>
        simp only [map_mul, map_pow, AdjoinRoot.mk_C,
          AdjoinRoot.mk_X, ← AdjoinRoot.algebraMap_eq]
        simpa only [s] using
          A.mul_mem (hcoeff a) (A.pow_mem hs (n + 1))
  apply Algebra.eq_top_iff.2
  intro z
  induction z using AdjoinRoot.induction_on with
  | ih p => exact hpolynomial p

/-- Integrality follows from the explicit monic degree-nine equation. -/
theorem primitiveElement_isIntegral : IsIntegral ℚ primitiveElement :=
  ⟨primitivePolynomial, primitivePolynomial_monic, primitiveElement_root⟩

/-- The power basis generated by `t - s`. -/
def primitivePowerBasis : PowerBasis ℚ M :=
  PowerBasis.ofAdjoinEqTop primitiveElement_isIntegral
    primitiveElement_adjoin_eq_top

@[simp]
theorem primitivePowerBasis_gen :
    primitivePowerBasis.gen = primitiveElement := by
  rw [primitivePowerBasis, PowerBasis.ofAdjoinEqTop_gen]

theorem primitiveElement_minpoly_natDegree :
    (minpoly ℚ primitiveElement).natDegree = 9 := by
  calc
    (minpoly ℚ primitiveElement).natDegree = primitivePowerBasis.dim := by
      simpa only [primitivePowerBasis_gen] using
        primitivePowerBasis.natDegree_minpoly
    _ = Module.finrank ℚ M := primitivePowerBasis.finrank.symm
    _ = 9 := finrank_M_over_rat

/-- The resultant polynomial is exactly the minimal polynomial, rather than
merely an annihilating polynomial. -/
theorem primitiveElement_minpoly :
    minpoly ℚ primitiveElement = primitivePolynomial := by
  exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le
    (minpoly.monic primitiveElement_isIntegral)
    primitivePolynomial_monic
    (minpoly.dvd ℚ primitiveElement primitiveElement_root)
    (by rw [primitivePolynomial_natDegree,
      primitiveElement_minpoly_natDegree])).symm

theorem primitivePolynomial_irreducible :
    Irreducible primitivePolynomial := by
  rw [← primitiveElement_minpoly]
  exact minpoly.irreducible primitiveElement_isIntegral







instance primitivePolynomial_irreducibleFact :
    Fact (Irreducible primitivePolynomial) :=
  ⟨primitivePolynomial_irreducible⟩

end

end MazurTorsion.XOneEighteenTwoDivisionPrimitive

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionSmallDiscriminant. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# A small-discriminant model of the `X₁(18)` two-division compositum

Starting from the primitive element `u = t - s`, this file constructs a
second generator with a substantially smaller defining polynomial.  Both
changes of generator are checked by explicit bounded polynomial identities.

The resulting power basis is a power basis over `ℚ`.  No assertion is made
that its integral span is the full ring of integers.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive

/-- The normalized degree-nine polynomial. -/
def normalizedPolynomial : Polynomial ℚ :=
  X ^ 9 - 3 * X ^ 8 + 7 * X ^ 6 - 3 * X ^ 5 - 9 * X ^ 4 +
    3 * X ^ 3 + 6 * X ^ 2 - 1

theorem normalizedPolynomial_monic : normalizedPolynomial.Monic := by
  simp only [normalizedPolynomial]
  monicity <;> norm_num

theorem normalizedPolynomial_natDegree :
    normalizedPolynomial.natDegree = 9 := by
  simp only [normalizedPolynomial]
  compute_degree!





















































































private def forwardNumerator : Polynomial ℚ :=
  X ^ 8 - 12 * X ^ 7 - 15 * X ^ 6 + 261 * X ^ 5 -
    243 * X ^ 4 - 1377 * X ^ 3 + 1377 * X ^ 2 - 3402 * X + 2673

/-- The forward change of generator, from `u` to the normalized generator. -/
def forwardPolynomial : Polynomial ℚ :=
  C (1 / 5346) * forwardNumerator

/-- The inverse change of generator. -/
def inversePolynomial : Polynomial ℚ :=
  -X ^ 6 + 4 * X ^ 5 - 4 * X ^ 4 - 4 * X ^ 3 +
    8 * X ^ 2 - 4

/-- The normalized generator in the degree-nine compositum. -/
def normalizedElement : M :=
  Polynomial.aeval primitiveElement forwardPolynomial



private def primitiveCertificateLeft : Polynomial ℚ :=
  X ^ 18 - 15 * X ^ 17 + 99 * X ^ 16 - 370 * X ^ 15 +
    822 * X ^ 14 - 951 * X ^ 13 - 38 * X ^ 12 + 1860 * X ^ 11 -
    2490 * X ^ 10 + 583 * X ^ 9 + 1911 * X ^ 8 - 2079 * X ^ 7 +
    325 * X ^ 6 + 729 * X ^ 5 - 417 * X ^ 4 - 18 * X ^ 3 +
    48 * X ^ 2 + 1

private def primitiveCertificateRight : Polynomial ℚ :=
  X ^ 27 - 18 * X ^ 26 + 144 * X ^ 25 - 648 * X ^ 24 +
    1632 * X ^ 23 - 1344 * X ^ 22 - 5118 * X ^ 21 +
    18660 * X ^ 20 - 19032 * X ^ 19 - 28109 * X ^ 18 +
    100284 * X ^ 17 - 69132 * X ^ 16 - 139269 * X ^ 15 +
    291906 * X ^ 14 - 44040 * X ^ 13 - 416277 * X ^ 12 +
    389016 * X ^ 11 + 236328 * X ^ 10 - 567261 * X ^ 9 +
    87198 * X ^ 8 + 428580 * X ^ 7 - 241218 * X ^ 6 -
    178008 * X ^ 5 + 178008 * X ^ 4 + 33333 * X ^ 3 -
    66666 * X ^ 2 + 11573

private def inverseCertificate : Polynomial ℚ :=
  X ^ 39 - 29 * X ^ 38 + 393 * X ^ 37 - 3276 * X ^ 36 +
    18538 * X ^ 35 - 73551 * X ^ 34 + 199718 * X ^ 33 -
    316038 * X ^ 32 - 9396 * X ^ 31 + 1492518 * X ^ 30 -
    3811884 * X ^ 29 + 3342246 * X ^ 28 + 5571187 * X ^ 27 -
    20469077 * X ^ 26 + 20282946 * X ^ 25 + 18324779 * X ^ 24 -
    72486147 * X ^ 23 + 59978295 * X ^ 22 + 62314925 * X ^ 21 -
    176704300 * X ^ 20 + 91592559 * X ^ 19 + 166289854 * X ^ 18 -
    278593602 * X ^ 17 + 39708081 * X ^ 16 + 278712309 * X ^ 15 -
    250996431 * X ^ 14 - 79815546 * X ^ 13 + 259471817 * X ^ 12 -
    96550462 * X ^ 11 - 117315852 * X ^ 10 + 114862674 * X ^ 9 +
    6336218 * X ^ 8 - 51676242 * X ^ 7 + 16470556 * X ^ 6 +
    9620757 * X ^ 5 - 6095061 * X ^ 4 - 229751 * X ^ 3 +
    551578 * X ^ 2 + 5346 * X + 2327

private abbrev NormalizedAdjoinRoot := AdjoinRoot normalizedPolynomial

private abbrev normalizedRoot : NormalizedAdjoinRoot :=
  AdjoinRoot.root normalizedPolynomial

private theorem normalizedRoot_root :
    Polynomial.aeval normalizedRoot normalizedPolynomial = 0 := by
  rw [aeval_def, AdjoinRoot.algebraMap_eq]
  exact AdjoinRoot.eval₂_root normalizedPolynomial

private theorem primitive_change_identity :
    primitivePolynomial.comp inversePolynomial =
      -primitiveCertificateLeft * primitiveCertificateRight *
        normalizedPolynomial := by
  simp only [primitivePolynomial, inversePolynomial, primitiveCertificateLeft,
    primitiveCertificateRight, normalizedPolynomial, add_comp, sub_comp,
    mul_comp, pow_comp, X_comp, ofNat_comp]
  ring

private theorem inverse_change_identity :
    forwardPolynomial.comp inversePolynomial - X =
      C (1 / 5346) * inverseCertificate * normalizedPolynomial := by
  have hnumerator :
      forwardNumerator.comp inversePolynomial - 5346 * X =
        inverseCertificate * normalizedPolynomial := by
    simp only [forwardNumerator, inversePolynomial, inverseCertificate,
      normalizedPolynomial, add_comp, sub_comp, mul_comp, pow_comp, X_comp,
      ofNat_comp]
    ring
  have hc : C (1 / 5346 : ℚ) * (5346 : Polynomial ℚ) = 1 := by
    change C (1 / 5346 : ℚ) * C (5346 : ℚ) = C (1 : ℚ)
    rw [← C_mul]
    norm_num
  have hscaled := congrArg
    (fun p : Polynomial ℚ ↦ C (1 / 5346) * p) hnumerator
  rw [mul_sub, ← mul_assoc, hc, one_mul] at hscaled
  simpa only [forwardPolynomial, mul_comp, C_comp, mul_assoc] using hscaled

private theorem primitive_of_inverse_root :
    Polynomial.aeval (Polynomial.aeval normalizedRoot inversePolynomial)
      primitivePolynomial = 0 := by
  rw [← Polynomial.aeval_comp, primitive_change_identity]
  simp only [map_mul, normalizedRoot_root, mul_zero]

private theorem forward_of_inverse_root :
    Polynomial.aeval
      (Polynomial.aeval normalizedRoot inversePolynomial) forwardPolynomial =
        normalizedRoot := by
  have h := congrArg (Polynomial.aeval normalizedRoot) inverse_change_identity
  simp only [map_sub, Polynomial.aeval_comp, aeval_X, map_mul, aeval_C,
    normalizedRoot_root, mul_zero] at h
  exact sub_eq_zero.mp h

/-- The explicit old-to-normalized change of presentation. -/
def primitiveToNormalizedHom :
    AdjoinRoot primitivePolynomial →ₐ[ℚ] AdjoinRoot normalizedPolynomial :=
  AdjoinRoot.liftAlgHom primitivePolynomial
    (Algebra.ofId ℚ (AdjoinRoot normalizedPolynomial))
    (Polynomial.aeval normalizedRoot inversePolynomial) (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      exact primitive_of_inverse_root)

@[simp]
theorem primitiveToNormalizedHom_root :
    primitiveToNormalizedHom (AdjoinRoot.root primitivePolynomial) =
      Polynomial.aeval normalizedRoot inversePolynomial := by
  exact AdjoinRoot.liftAlgHom_root primitivePolynomial _ _ _

private theorem primitiveToNormalizedHom_forward :
    primitiveToNormalizedHom
        (Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
          forwardPolynomial) = normalizedRoot := by
  rw [← Polynomial.aeval_algHom_apply, primitiveToNormalizedHom_root]
  exact forward_of_inverse_root

private instance normalizedAdjoinRootNontrivial :
    Nontrivial (AdjoinRoot normalizedPolynomial) := by
  apply AdjoinRoot.nontrivial
  rw [degree_eq_natDegree normalizedPolynomial_monic.ne_zero,
    normalizedPolynomial_natDegree]
  norm_num

private theorem primitiveToNormalizedHom_injective :
    Function.Injective primitiveToNormalizedHom := by
  exact RingHom.injective primitiveToNormalizedHom.toRingHom

private theorem primitiveToNormalizedHom_surjective :
    Function.Surjective primitiveToNormalizedHom := by
  apply (AlgHom.range_eq_top primitiveToNormalizedHom).mp
  rw [← top_le_iff, ← AdjoinRoot.adjoinRoot_eq_top]
  apply Algebra.adjoin_le
  rw [Set.singleton_subset_iff]
  exact (AlgHom.mem_range primitiveToNormalizedHom).2
    ⟨Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
      forwardPolynomial, primitiveToNormalizedHom_forward⟩

/-- The two explicit changes of generator give an equivalence between the
old and normalized quotient presentations. -/
def primitiveToNormalizedEquiv :
    AdjoinRoot primitivePolynomial ≃ₐ[ℚ] AdjoinRoot normalizedPolynomial :=
  AlgEquiv.ofBijective primitiveToNormalizedHom
    ⟨primitiveToNormalizedHom_injective,
      primitiveToNormalizedHom_surjective⟩

@[simp]
theorem primitiveToNormalizedEquiv_root :
    primitiveToNormalizedEquiv (AdjoinRoot.root primitivePolynomial) =
      Polynomial.aeval normalizedRoot inversePolynomial := by
  exact primitiveToNormalizedHom_root

private theorem primitiveToNormalizedEquiv_symm_root :
    primitiveToNormalizedEquiv.symm normalizedRoot =
      Polynomial.aeval (AdjoinRoot.root primitivePolynomial)
        forwardPolynomial := by
  apply primitiveToNormalizedEquiv.injective
  rw [primitiveToNormalizedEquiv.apply_symm_apply]
  exact primitiveToNormalizedHom_forward.symm

private def primitivePresentationHom :
    AdjoinRoot primitivePolynomial →ₐ[ℚ] M :=
  AdjoinRoot.liftAlgHom primitivePolynomial (Algebra.ofId ℚ M)
    primitiveElement (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      exact primitiveElement_root)

@[simp]
private theorem primitivePresentationHom_root :
    primitivePresentationHom (AdjoinRoot.root primitivePolynomial) =
      primitiveElement := by
  exact AdjoinRoot.liftAlgHom_root primitivePolynomial _ _ _

private theorem primitivePresentationHom_injective :
    Function.Injective primitivePresentationHom := by
  exact RingHom.injective primitivePresentationHom.toRingHom

private theorem primitivePresentationHom_surjective :
    Function.Surjective primitivePresentationHom := by
  apply (AlgHom.range_eq_top primitivePresentationHom).mp
  rw [← top_le_iff, ← primitiveElement_adjoin_eq_top]
  apply Algebra.adjoin_le
  rw [Set.singleton_subset_iff]
  exact (AlgHom.mem_range primitivePresentationHom).2
    ⟨AdjoinRoot.root primitivePolynomial, primitivePresentationHom_root⟩

private def primitivePresentationEquiv :
    AdjoinRoot primitivePolynomial ≃ₐ[ℚ] M :=
  AlgEquiv.ofBijective primitivePresentationHom
    ⟨primitivePresentationHom_injective,
      primitivePresentationHom_surjective⟩

@[simp]
private theorem primitivePresentationEquiv_root :
    primitivePresentationEquiv (AdjoinRoot.root primitivePolynomial) =
      primitiveElement := by
  exact primitivePresentationHom_root

/-- The normalized polynomial quotient is the original degree-nine
two-division compositum. -/
def normalizedAdjoinRootEquiv :
    AdjoinRoot normalizedPolynomial ≃ₐ[ℚ] M :=
  primitiveToNormalizedEquiv.symm.trans primitivePresentationEquiv

@[simp]
theorem normalizedAdjoinRootEquiv_root :
    normalizedAdjoinRootEquiv normalizedRoot = normalizedElement := by
  rw [normalizedAdjoinRootEquiv, AlgEquiv.trans_apply,
    primitiveToNormalizedEquiv_symm_root]
  rw [← Polynomial.aeval_algHom_apply, primitivePresentationEquiv_root]
  rfl

/-- The normalized generator satisfies the advertised small polynomial. -/
theorem normalizedElement_root :
    Polynomial.aeval normalizedElement normalizedPolynomial = 0 := by
  rw [← normalizedAdjoinRootEquiv_root,
    Polynomial.aeval_algHom_apply, normalizedRoot_root, map_zero]

/-- The inverse polynomial recovers `u = t - s` from the normalized
generator. -/
theorem normalizedElement_reconstruction :
    Polynomial.aeval normalizedElement inversePolynomial =
      primitiveElement := by
  rw [← normalizedAdjoinRootEquiv_root,
    Polynomial.aeval_algHom_apply]
  change primitivePresentationEquiv
      (primitiveToNormalizedEquiv.symm
        (Polynomial.aeval normalizedRoot inversePolynomial)) =
    primitiveElement
  rw [← primitiveToNormalizedEquiv_root,
    primitiveToNormalizedEquiv.symm_apply_apply,
    primitivePresentationEquiv_root]



















end

end MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionIntegralElements. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Integral elements in the `X₁(18)` two-division compositum

This file expresses the explicit descent generators as integer polynomials in
the normalized algebraic integer.  The identities are checked by bounded
polynomial reduction modulo its monic degree-nine equation.  They therefore
do not assume that the normalized power order is the full ring of integers.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralElements

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel

/-- The coefficient-field generator as a reduced polynomial in the
normalized generator. -/
def coefficientPolynomial : Polynomial ℚ :=
  -X ^ 8 + 4 * X ^ 7 - 5 * X ^ 6 + 5 * X ^ 4 -
    2 * X ^ 3 - X ^ 2 + 2 * X - 1

/-- The relative cubic generator as a reduced polynomial in the normalized
generator. -/
def relativePolynomialInNormalized : Polynomial ℚ :=
  -X ^ 8 + 4 * X ^ 7 - 4 * X ^ 6 - 4 * X ^ 5 +
    9 * X ^ 4 + 2 * X ^ 3 - 9 * X ^ 2 + 2 * X + 3

private def coefficientGeneratorNumerator : Polynomial ℚ :=
  1944 - 1944 * X + 2511 * X ^ 2 - 810 * X ^ 3 +
    135 * X ^ 4 + 216 * X ^ 5 - 72 * X ^ 6 - 6 * X ^ 7 + 4 * X ^ 8

private theorem coefficientGeneratorPolynomial_eq :
    coefficientGeneratorPolynomial =
      C (1 / 2673) * coefficientGeneratorNumerator := by
  rfl

private def coefficientReductionQuotient : Polynomial ℚ :=
  4 * X ^ 39 - 116 * X ^ 38 + 1572 * X ^ 37 - 13104 * X ^ 36 +
      74152 * X ^ 35 - 294204 * X ^ 34 + 798830 * X ^ 33 -
      1263102 * X ^ 32 - 49722 * X ^ 31 + 6055080 * X ^ 30 -
      15642084 * X ^ 29 + 14596854 * X ^ 28 + 19949788 * X ^ 27 -
      80612276 * X ^ 26 + 88045260 * X ^ 25 + 51038096 * X ^ 24 -
      264079212 * X ^ 23 + 255207684 * X ^ 22 + 154030532 * X ^ 21 -
      590624884 * X ^ 20 + 397288638 * X ^ 19 + 407446306 * X ^ 18 -
      857304078 * X ^ 17 + 263874420 * X ^ 16 + 664663143 * X ^ 15 -
      718287213 * X ^ 14 - 76011993 * X ^ 13 + 580162460 * X ^ 12 -
      272499070 * X ^ 11 - 202705341 * X ^ 10 + 234062868 * X ^ 9 -
      6549256 * X ^ 8 - 86738118 * X ^ 7 + 30274846 * X ^ 6 +
      13634238 * X ^ 5 - 9014574 * X ^ 4 - 215009 * X ^ 3 +
      680953 * X ^ 2 + 5346 * X + 16679

private theorem coefficientNumerator_comp_inverse_identity :
    coefficientGeneratorNumerator.comp inversePolynomial =
      2673 * coefficientPolynomial +
        coefficientReductionQuotient * normalizedPolynomial := by
  simp only [coefficientGeneratorNumerator, inversePolynomial,
    coefficientPolynomial, coefficientReductionQuotient,
    normalizedPolynomial, add_comp, sub_comp, mul_comp, pow_comp,
    X_comp, ofNat_comp]
  ring

/-- Reconstruction of the coefficient-field generator from the normalized
integral generator. -/
theorem coefficientGenerator_formula :
    t = Polynomial.aeval normalizedElement coefficientPolynomial := by
  rw [← coefficientGenerator_reconstruction,
    coefficientGeneratorPolynomial_eq, map_mul, aeval_C,
    ← normalizedElement_reconstruction, ← Polynomial.aeval_comp]
  rw [coefficientNumerator_comp_inverse_identity]
  simp only [map_add, map_mul, map_ofNat, normalizedElement_root,
    mul_zero, add_zero]
  rw [map_div₀, map_one, map_ofNat]
  field_simp

/-- Reconstruction of the relative generator from the normalized integral
generator. -/
theorem relativeGenerator_formula :
    s = Polynomial.aeval normalizedElement relativePolynomialInNormalized := by
  calc
    s = t - primitiveElement := by simp only [primitiveElement]; ring
    _ = Polynomial.aeval normalizedElement coefficientPolynomial -
        Polynomial.aeval normalizedElement inversePolynomial := by
      rw [coefficientGenerator_formula, normalizedElement_reconstruction]
    _ = Polynomial.aeval normalizedElement
        (coefficientPolynomial - inversePolynomial) := by rw [map_sub]
    _ = Polynomial.aeval normalizedElement
        relativePolynomialInNormalized := by
      congr 1
      simp only [coefficientPolynomial, inversePolynomial,
        relativePolynomialInNormalized]
      ring

private theorem scaled_aeval_of_reduction (n : ℕ) (hn : n ≠ 0)
    {raw target quotient : Polynomial ℚ}
    (hred : raw = n * target + quotient * normalizedPolynomial) :
    (1 / (n : M)) * Polynomial.aeval normalizedElement raw =
      Polynomial.aeval normalizedElement target := by
  rw [hred]
  simp only [map_add, map_mul, map_natCast, normalizedElement_root,
    mul_zero, add_zero, div_eq_mul_inv, one_mul]
  have hnM : (n : M) ≠ 0 := by exact_mod_cast hn
  rw [← mul_assoc, inv_mul_cancel₀ hnM, one_mul]

/-! ## Integral polynomial representatives -/

























private def betaReductionQuotient : Polynomial ℚ :=
  -X ^ 23 + 13 * X ^ 22 - 75 * X ^ 21 + 246 * X ^ 20 -
    473 * X ^ 19 + 424 * X ^ 18 + 247 * X ^ 17 - 1106 * X ^ 16 +
    881 * X ^ 15 + 836 * X ^ 14 - 2267 * X ^ 13 +
    1412 * X ^ 12 + 937 * X ^ 11 - 2042 * X ^ 10 + 881 * X ^ 9 +
    888 * X ^ 8 - 1403 * X ^ 7 + 580 * X ^ 6 + 387 * X ^ 5 -
    610 * X ^ 4 + 266 * X ^ 3 + 35 * X ^ 2 - 96 * X + 40























/-- Integer polynomial representing `h1`. -/
def h1PolynomialInt : Polynomial ℤ :=
  -X ^ 8 + 3 * X ^ 7 - 8 * X ^ 5 + 6 * X ^ 4 +
    8 * X ^ 3 - 7 * X ^ 2 - 3 * X + 3

private def h1Polynomial : Polynomial ℚ :=
  -X ^ 8 + 3 * X ^ 7 - 8 * X ^ 5 + 6 * X ^ 4 +
    8 * X ^ 3 - 7 * X ^ 2 - 3 * X + 3

theorem h1PolynomialInt_map :
    h1PolynomialInt.map (algebraMap ℤ ℚ) = h1Polynomial := by
  norm_num [h1PolynomialInt, h1Polynomial]

private def h1Numerator : Polynomial ℚ :=
  (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 2) *
      relativePolynomialInNormalized ^ 2 +
    (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 8) *
      relativePolynomialInNormalized +
    2 * (4 * coefficientPolynomial ^ 2 - 5 * coefficientPolynomial - 5)

private theorem h1_reduction_identity :
    h1Numerator = 18 * h1Polynomial +
      betaReductionQuotient * normalizedPolynomial := by
  simp only [h1Numerator, h1Polynomial, betaReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem h1_formula_rat :
    h1 = Polynomial.aeval normalizedElement h1Polynomial := by
  calc
    h1 = (1 / 18 : M) *
        Polynomial.aeval normalizedElement h1Numerator := by
      rw [h1, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_neg]
      change ((-t ^ 2 + 2 * t + 2) / 18) * s ^ 2 +
          ((-t ^ 2 + 2 * t + 8) / 18) * s +
          ((4 * t ^ 2 - 5 * t - 5) / 9) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [h1Numerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement h1Polynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        h1_reduction_identity

/-- The first norm-one generator is the value of an integer polynomial in
the normalized algebraic integer. -/
theorem h1_formula :
    h1 = Polynomial.aeval normalizedElement h1PolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    h1PolynomialInt, h1PolynomialInt_map]
  exact h1_formula_rat

/-- Integer polynomial representing `h2`. -/
def h2PolynomialInt : Polynomial ℤ :=
  -X ^ 6 + 3 * X ^ 5 - X ^ 4 - 4 * X ^ 3 + 3 * X ^ 2 + 3 * X - 1

private def h2Polynomial : Polynomial ℚ :=
  -X ^ 6 + 3 * X ^ 5 - X ^ 4 - 4 * X ^ 3 + 3 * X ^ 2 + 3 * X - 1

theorem h2PolynomialInt_map :
    h2PolynomialInt.map (algebraMap ℤ ℚ) = h2Polynomial := by
  norm_num [h2PolynomialInt, h2Polynomial]

private def h2Numerator : Polynomial ℚ :=
  relativePolynomialInNormalized ^ 2 + relativePolynomialInNormalized +
    2 * (coefficientPolynomial ^ 2 + coefficientPolynomial) - 6

private def h2ReductionQuotient : Polynomial ℚ :=
  3 * X ^ 7 - 15 * X ^ 6 + 31 * X ^ 5 - 32 * X ^ 4 +
    14 * X ^ 3 - 5 * X ^ 2 + 8 * X - 12

private theorem h2_reduction_identity :
    h2Numerator = 6 * h2Polynomial +
      h2ReductionQuotient * normalizedPolynomial := by
  simp only [h2Numerator, h2Polynomial, h2ReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem h2_formula_rat :
    h2 = Polynomial.aeval normalizedElement h2Polynomial := by
  calc
    h2 = (1 / 6 : M) *
        Polynomial.aeval normalizedElement h2Numerator := by
      rw [h2, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_pow, map_ofNat, map_one]
      change (1 / 6 : M) * s ^ 2 + (1 / 6 : M) * s +
          ((t ^ 2 + t) / 3 - 1) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [h2Numerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat]
      ring
    _ = Polynomial.aeval normalizedElement h2Polynomial := by
      exact scaled_aeval_of_reduction 6 (by norm_num)
        h2_reduction_identity

/-- The second norm-one generator is the value of an integer polynomial in
the normalized algebraic integer. -/
theorem h2_formula :
    h2 = Polynomial.aeval normalizedElement h2PolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    h2PolynomialInt, h2PolynomialInt_map]
  exact h2_formula_rat

/-- Integer polynomial representing `h3`. -/
def h3PolynomialInt : Polynomial ℤ :=
  -(X ^ 3 - X ^ 2 + 1) *
    (X ^ 5 - 3 * X ^ 4 + X ^ 3 + 4 * X ^ 2 - 3 * X - 4)

private def h3Polynomial : Polynomial ℚ :=
  -(X ^ 3 - X ^ 2 + 1) *
    (X ^ 5 - 3 * X ^ 4 + X ^ 3 + 4 * X ^ 2 - 3 * X - 4)

theorem h3PolynomialInt_map :
    h3PolynomialInt.map (algebraMap ℤ ℚ) = h3Polynomial := by
  norm_num [h3PolynomialInt, h3Polynomial]

private def h3Numerator : Polynomial ℚ :=
  (2 * coefficientPolynomial ^ 2 - coefficientPolynomial + 2) *
      relativePolynomialInNormalized ^ 2 +
    (2 * coefficientPolynomial ^ 2 - 7 * coefficientPolynomial + 14) *
      relativePolynomialInNormalized +
    2 * (4 * coefficientPolynomial ^ 2 - 5 * coefficientPolynomial + 4)

private def h3ReductionQuotient : Polynomial ℚ :=
  2 * X ^ 23 - 26 * X ^ 22 + 150 * X ^ 21 - 492 * X ^ 20 +
    946 * X ^ 19 - 848 * X ^ 18 - 494 * X ^ 17 + 2212 * X ^ 16 -
    1765 * X ^ 15 - 1645 * X ^ 14 + 4432 * X ^ 13 -
    2629 * X ^ 12 - 2018 * X ^ 11 + 3946 * X ^ 10 -
    1414 * X ^ 9 - 1866 * X ^ 8 + 2428 * X ^ 7 - 812 * X ^ 6 -
    579 * X ^ 5 + 677 * X ^ 4 - 166 * X ^ 3 - 163 * X ^ 2 +
    156 * X - 68

private theorem h3_reduction_identity :
    h3Numerator = 18 * h3Polynomial +
      h3ReductionQuotient * normalizedPolynomial := by
  simp only [h3Numerator, h3Polynomial, h3ReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem h3_formula_rat :
    h3 = Polynomial.aeval normalizedElement h3Polynomial := by
  calc
    h3 = (1 / 18 : M) *
        Polynomial.aeval normalizedElement h3Numerator := by
      rw [h3, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat]
      change ((2 * t ^ 2 - t + 2) / 18) * s ^ 2 +
          ((2 * t ^ 2 - 7 * t + 14) / 18) * s +
          ((4 * t ^ 2 - 5 * t + 4) / 9) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [h3Numerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat]
      ring
    _ = Polynomial.aeval normalizedElement h3Polynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        h3_reduction_identity

/-- The first norm-four generator is the value of an integer polynomial in
the normalized algebraic integer. -/
theorem h3_formula :
    h3 = Polynomial.aeval normalizedElement h3PolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    h3PolynomialInt, h3PolynomialInt_map]
  exact h3_formula_rat

/-- Integer polynomial representing `h4`. -/
def h4PolynomialInt : Polynomial ℤ :=
  -(X ^ 3 - 2 * X ^ 2 + X + 1) * (X ^ 3 - X ^ 2 - 2 * X - 1)

private def h4Polynomial : Polynomial ℚ :=
  -(X ^ 3 - 2 * X ^ 2 + X + 1) * (X ^ 3 - X ^ 2 - 2 * X - 1)

theorem h4PolynomialInt_map :
    h4PolynomialInt.map (algebraMap ℤ ℚ) = h4Polynomial := by
  norm_num [h4PolynomialInt, h4Polynomial]

private def h4Numerator : Polynomial ℚ :=
  (-coefficientPolynomial ^ 2 + 3) * relativePolynomialInNormalized ^ 2 +
    (coefficientPolynomial ^ 2 + 1) * relativePolynomialInNormalized +
    6 * coefficientPolynomial ^ 2 - 10

private def h4ReductionQuotient : Polynomial ℚ :=
  -X ^ 23 + 13 * X ^ 22 - 75 * X ^ 21 + 246 * X ^ 20 -
    473 * X ^ 19 + 424 * X ^ 18 + 247 * X ^ 17 - 1106 * X ^ 16 +
    881 * X ^ 15 + 836 * X ^ 14 - 2269 * X ^ 13 +
    1430 * X ^ 12 + 869 * X ^ 11 - 1912 * X ^ 10 + 783 * X ^ 9 +
    802 * X ^ 8 - 1164 * X ^ 7 + 459 * X ^ 6 + 232 * X ^ 5 -
    356 * X ^ 4 + 148 * X ^ 3 - 10 * X - 14

private theorem h4_reduction_identity :
    h4Numerator = 6 * h4Polynomial +
      h4ReductionQuotient * normalizedPolynomial := by
  simp only [h4Numerator, h4Polynomial, h4ReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem h4_formula_rat :
    h4 = Polynomial.aeval normalizedElement h4Polynomial := by
  calc
    h4 = (1 / 6 : M) *
        Polynomial.aeval normalizedElement h4Numerator := by
      rw [h4, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_pow, map_ofNat,
        map_one, map_neg]
      change ((-t ^ 2 + 3) / 6) * s ^ 2 +
          ((t ^ 2 + 1) / 6) * s + (t ^ 2 - 5 / 3) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [h4Numerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_one, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement h4Polynomial := by
      exact scaled_aeval_of_reduction 6 (by norm_num)
        h4_reduction_identity

/-- The final kernel generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem h4_formula :
    h4 = Polynomial.aeval normalizedElement h4PolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    h4PolynomialInt, h4PolynomialInt_map]
  exact h4_formula_rat













































































end

end MazurTorsion.XOneEighteenTwoDivisionIntegralElements

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionTriadicLift. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The triadic prime in the `X₁(18)` two-division compositum

The normalized integral generator has a relative cubic polynomial over the
real cubic coefficient field.  Its discriminant is `-8`, so reduction at the
unique coefficient prime above `3` is controlled by Kummer--Dedekind.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionTriadicLift

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrimitive
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionTriadicPrime
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## The relative normalized polynomial -/

/-- The relative cubic polynomial of the normalized generator over the
coefficient field. -/
def normalizedRelativePolynomial : Polynomial Q.K :=
  X ^ 3 + C (Q.tau ^ 2 - 3) * X ^ 2 +
    C (-2 * Q.tau ^ 2 + Q.tau + 4) * X - 1





private def normalizedRelativeExpression : Polynomial ℚ :=
  X ^ 3 + (coefficientPolynomial ^ 2 - 3) * X ^ 2 +
    (-2 * coefficientPolynomial ^ 2 + coefficientPolynomial + 4) * X - 1

private def normalizedRelativeReductionQuotient : Polynomial ℚ :=
  X ^ 9 - 7 * X ^ 8 + 21 * X ^ 7 - 36 * X ^ 6 +
    39 * X ^ 5 - 28 * X ^ 4 + 13 * X ^ 3 -
    2 * X ^ 2 - X + 1

private theorem normalizedRelative_reduction_identity :
    normalizedRelativeExpression =
      normalizedRelativeReductionQuotient * normalizedPolynomial := by
  simp only [normalizedRelativeExpression,
    normalizedRelativeReductionQuotient, coefficientPolynomial,
    normalizedPolynomial]
  ring

private theorem normalizedRelativeExpression_root :
    Polynomial.aeval normalizedElement normalizedRelativeExpression = 0 := by
  rw [normalizedRelative_reduction_identity]
  simp only [map_mul, normalizedElement_root, mul_zero]

/-- The normalized generator satisfies the displayed relative cubic. -/
theorem normalizedElement_relative_root :
    Polynomial.aeval normalizedElement normalizedRelativePolynomial = 0 := by
  simp only [normalizedRelativePolynomial, map_sub, map_add, map_mul,
    map_pow, aeval_X, aeval_C, map_neg, map_one, map_ofNat]
  change normalizedElement ^ 3 +
      (t ^ 2 - 3) * normalizedElement ^ 2 +
      (-2 * t ^ 2 + t + 4) * normalizedElement - 1 = 0
  rw [coefficientGenerator_formula]
  simpa only [normalizedRelativeExpression, map_sub, map_add, map_mul,
    map_pow, map_ofNat, map_neg, map_one, aeval_X] using
    normalizedRelativeExpression_root

















/-! ## A relative power basis with discriminant `-8` -/





















/-! ## The integral relative polynomial -/

/-- The same relative polynomial over the coefficient ring of integers. -/
def normalizedRelativePolynomialInteger :
    Polynomial (NumberField.RingOfIntegers Q.K) :=
  X ^ 3 + C (coefficientInteger ^ 2 - 3) * X ^ 2 +
    C (-2 * coefficientInteger ^ 2 + coefficientInteger + 4) * X - 1

theorem normalizedRelativePolynomialInteger_monic :
    normalizedRelativePolynomialInteger.Monic := by
  simp only [normalizedRelativePolynomialInteger]
  monicity <;> norm_num

theorem normalizedRelativePolynomialInteger_map :
    normalizedRelativePolynomialInteger.map
        (algebraMap (NumberField.RingOfIntegers Q.K) Q.K) =
      normalizedRelativePolynomial := by
  have hcoefficient :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K
          coefficientInteger = Q.tau := rfl
  have htwo :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 2 = 2 := by
    exact map_ofNat _ 2
  have hthree :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 3 = 3 := by
    exact map_ofNat _ 3
  have hfour :
      algebraMap (NumberField.RingOfIntegers Q.K) Q.K 4 = 4 := by
    exact map_ofNat _ 4
  simp [normalizedRelativePolynomialInteger,
    normalizedRelativePolynomial, hcoefficient, htwo, hthree, hfour]



/-! ## Relative conductor control at the coefficient prime -/





/-! ## Irreducible reduction at the triadic coefficient prime -/

























/-! ## The unique triadic prime in the compositum -/









end

end MazurTorsion.XOneEighteenTwoDivisionTriadicLift

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

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

/-! ## The actual dyadic prime of the coefficient field -/

















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

/-- Approximation by a global integer at an arbitrary integral adic
precision.  This is the higher-precision form of
`HeightOneSpectrum.exists_valued_sub_lt_one`. -/
theorem exists_valued_sub_lt_exp_neg
    (v : HeightOneSpectrum R) (x : v.adicCompletionIntegers K) (n : ℕ) :
    ∃ a : R,
      Valued.v ((x : v.adicCompletion K) -
          algebraMap R (v.adicCompletion K) a) < exp (-(n : ℤ)) := by
  have hball :
      {y : v.adicCompletion K |
          Valued.v (y - (x : v.adicCompletion K)) < exp (-(n : ℤ))} ∈
        nhds (x : v.adicCompletion K) := by
    obtain ⟨w, hw⟩ :=
      v.valuedAdicCompletion_surjective K (exp (-(n : ℤ)))
    have hwne : w ≠ 0 := by
      intro hwzero
      rw [hwzero, map_zero] at hw
      exact exp_ne_zero hw.symm
    rw [Valued.mem_nhds]
    refine ⟨Units.mk0 (Valued.v.restrict w)
      (Valued.v.restrict.ne_zero_iff.mpr hwne), ?_⟩
    intro y hy
    simpa only [Valuation.restrict_lt_iff_lt_embedding, Units.val_mk0,
      Valuation.embedding_restrict, hw] using hy
  obtain ⟨_, hwball, z, rfl⟩ :=
    mem_closure_iff_nhds.mp
      (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap
        (K := K) v _) _ hball
  rw [Set.mem_setOf_eq] at hwball
  have hexp_le_one : exp (-(n : ℤ)) ≤ (1 : ℤᵐ⁰) := by
    rw [← exp_zero, exp_le_exp]
    omega
  have hz1 : v.valuation K z ≤ 1 := by
    rw [show v.valuation K z =
      Valued.v (algebraMap K (v.adicCompletion K) z) from
        (v.valuedAdicCompletion_eq_valuation' z).symm]
    calc
      Valued.v (algebraMap K (v.adicCompletion K) z) =
          Valued.v
            (algebraMap K (v.adicCompletion K) z -
                (x : v.adicCompletion K) + (x : v.adicCompletion K)) := by
            ring_nf
      _ ≤ max
          (Valued.v (algebraMap K (v.adicCompletion K) z -
            (x : v.adicCompletion K)))
          (Valued.v (x : v.adicCompletion K)) :=
        Valuation.map_add _ _ _
      _ ≤ 1 := max_le (hwball.le.trans hexp_le_one) x.2
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hz1
    (WithZero.expOrderIso (-(n : ℤ)))
  refine ⟨a, ?_⟩
  have ha' :
      Valued.v (algebraMap K (v.adicCompletion K) z -
          algebraMap R (v.adicCompletion K) a) < exp (-(n : ℤ)) := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K), ← map_sub,
      show Valued.v
          (algebraMap K (v.adicCompletion K)
            (z - algebraMap R K a)) =
          v.valuation K (z - algebraMap R K a) from
        v.valuedAdicCompletion_eq_valuation' _,
      Valuation.map_sub_swap]
    exact ha
  calc
    Valued.v ((x : v.adicCompletion K) -
        algebraMap R (v.adicCompletion K) a) =
      Valued.v
        (((x : v.adicCompletion K) -
            algebraMap K (v.adicCompletion K) z) +
          (algebraMap K (v.adicCompletion K) z -
            algebraMap R (v.adicCompletion K) a)) := by ring_nf
    _ ≤ max _ _ := Valuation.map_add _ _ _
    _ < exp (-(n : ℤ)) :=
      max_lt (by rwa [Valuation.map_sub_swap] at hwball) ha'

/-- The canonical map from a global prime-power quotient to the
corresponding quotient of the completion's integers. -/
def completionQuotientMap (v : HeightOneSpectrum R) (n : ℕ) :
    R ⧸ v.asIdeal ^ n →+*
      v.adicCompletionIntegers K ⧸
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :=
  Ideal.quotientMap
    (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
    (algebraMap R (v.adicCompletionIntegers K)) (by
      intro r hr
      exact (v.algebraMap_mem_maximalIdeal_pow_iff (K := K)).2 hr)

theorem completionQuotientMap_bijective
    (v : HeightOneSpectrum R) (n : ℕ) :
    Function.Bijective (completionQuotientMap (K := K) v n) := by
  constructor
  · apply Ideal.quotientMap_injective'
    intro r hr
    exact (v.algebraMap_mem_maximalIdeal_pow_iff (K := K)).1 hr
  · intro y
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨a, ha⟩ := exists_valued_sub_lt_exp_neg v x n
    refine ⟨Ideal.Quotient.mk (v.asIdeal ^ n) a, ?_⟩
    change
      Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
          (algebraMap R (v.adicCompletionIntegers K) a) =
        Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n) x
    apply Ideal.Quotient.eq.mpr
    apply (v.mem_maximalIdeal_pow_iff (K := K)).2
    change Valued.v
      (algebraMap R (v.adicCompletion K) a -
        (x : v.adicCompletion K)) ≤ exp (-(n : ℤ))
    rw [Valuation.map_sub_swap]
    exact ha.le

/-- Quotienting a Dedekind domain by `v^n` is canonically equivalent to
quotienting the integer ring of its adic completion by `m_v^n`. -/
noncomputable def completionQuotientEquiv
    (v : HeightOneSpectrum R) (n : ℕ) :
    R ⧸ v.asIdeal ^ n ≃+*
      v.adicCompletionIntegers K ⧸
        IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n :=
  RingEquiv.ofBijective (completionQuotientMap (K := K) v n)
    (completionQuotientMap_bijective (K := K) v n)

@[simp] theorem completionQuotientEquiv_mk
    (v : HeightOneSpectrum R) (n : ℕ) (r : R) :
    completionQuotientEquiv (K := K) v n
        (Ideal.Quotient.mk (v.asIdeal ^ n) r) =
      Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n)
        (algebraMap R (v.adicCompletionIntegers K) r) := by
  rfl

end CompletionQuotient

/-! ## The coefficient completion modulo `2⁷` -/

open MazurTorsion.XOneEighteenDyadicLocalImage

/-- The seventh-power quotient at the genuine dyadic prime. -/
abbrev CoefficientDyadicQuotient :=
  𝓞 Q.K ⧸ coefficientPrimeTwo.asIdeal ^ 7

theorem coefficientPrimeTwo_pow_seven :
    coefficientPrimeTwo.asIdeal ^ 7 = Ideal.span {(128 : 𝓞 Q.K)} := by
  rw [coefficientPrimeTwo_span, Ideal.span_singleton_pow]
  norm_num

private theorem span_one_twenty_eight_le_comap :
    Ideal.span {(128 : ℤ)} ≤
      Ideal.comap (algebraMap ℤ (𝓞 Q.K))
        (coefficientPrimeTwo.asIdeal ^ 7) := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap,
    coefficientPrimeTwo_pow_seven]
  exact Ideal.subset_span (Set.mem_singleton 128)

/-- The canonical scalar map from `ZMod 128` into the global dyadic
quotient. -/
def coefficientBaseMod128 : ZMod 128 →+* CoefficientDyadicQuotient :=
  (Ideal.quotientMap (coefficientPrimeTwo.asIdeal ^ 7)
      (algebraMap ℤ (𝓞 Q.K)) span_one_twenty_eight_le_comap).comp
    ((Int.quotientSpanNatEquivZMod 128).symm :
      ZMod 128 →+* ℤ ⧸ Ideal.span {(128 : ℤ)})

@[simp] theorem coefficientBaseMod128_intCast (z : ℤ) :
    coefficientBaseMod128 (z : ZMod 128) =
      Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)
        (algebraMap ℤ (𝓞 Q.K) z) := by
  change
    (Ideal.quotientMap (coefficientPrimeTwo.asIdeal ^ 7)
        (algebraMap ℤ (𝓞 Q.K)) span_one_twenty_eight_le_comap)
      ((Int.quotientSpanNatEquivZMod 128).symm (z : ZMod 128)) = _
  have hz := congrArg
    (fun f : ℤ →+* ℤ ⧸ Ideal.span {(128 : ℤ)} ↦ f z)
    (Int.quotientSpanNatEquivZMod_comp_castRingHom 128)
  simp only [RingHom.comp_apply] at hz
  change
    (Ideal.quotientMap (coefficientPrimeTwo.asIdeal ^ 7)
        (algebraMap ℤ (𝓞 Q.K)) span_one_twenty_eight_le_comap)
      ((Int.quotientSpanNatEquivZMod 128).symm
        ((Int.castRingHom (ZMod 128)) z)) = _
  calc
    _ = (Ideal.quotientMap (coefficientPrimeTwo.asIdeal ^ 7)
          (algebraMap ℤ (𝓞 Q.K)) span_one_twenty_eight_le_comap)
        (Ideal.Quotient.mk (Ideal.span {(128 : ℤ)}) z) :=
      congrArg _ hz
    _ = _ := Ideal.quotientMap_mk

private theorem coefficientBaseMod128_comp_intCast :
    coefficientBaseMod128.comp (Int.castRingHom (ZMod 128)) =
      (Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)).comp
        (algebraMap ℤ (𝓞 Q.K)) := by
  ext z
  exact coefficientBaseMod128_intCast z

/-- The image of the coefficient-field generator in the dyadic quotient. -/
def coefficientTauMod128 : CoefficientDyadicQuotient :=
  Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7) coefficientInteger

private theorem coefficientInteger_cubic :
    coefficientInteger ^ 3 - 3 * coefficientInteger - 1 = 0 := by
  have hmin := minpoly.aeval ℤ coefficientInteger
  rw [coefficientInteger_minpoly] at hmin
  simpa only [coefficientPolynomialInt, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat, map_one] using hmin

theorem coefficientTauMod128_cubic :
    coefficientTauMod128 ^ 3 - 3 * coefficientTauMod128 - 1 = 0 := by
  simp only [coefficientTauMod128]
  rw [← map_pow, ← map_ofNat
      (Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)) 3,
    ← map_mul, ← map_one
      (Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)),
    ← map_sub, ← map_sub, coefficientInteger_cubic, map_zero]

private theorem cubicPolynomial128_eval₂_coefficientTau :
    cubicPolynomial128.eval₂ coefficientBaseMod128 coefficientTauMod128 = 0 := by
  simp only [cubicPolynomial128, eval₂_sub, eval₂_pow, eval₂_X,
    eval₂_mul, eval₂_ofNat, eval₂_one]
  exact coefficientTauMod128_cubic

/-- Evaluation of the monogenic cubic order in the global dyadic
quotient. -/
def cubicToGlobalDyadic : CubicResidue128 →+* CoefficientDyadicQuotient :=
  AdjoinRoot.lift coefficientBaseMod128 coefficientTauMod128
    cubicPolynomial128_eval₂_coefficientTau

@[simp] theorem cubicToGlobalDyadic_root :
    cubicToGlobalDyadic (AdjoinRoot.root cubicPolynomial128) =
      coefficientTauMod128 := by
  exact AdjoinRoot.lift_root cubicPolynomial128_eval₂_coefficientTau

theorem cubicToGlobalDyadic_mk_map_int
    (p : Polynomial ℤ) :
    cubicToGlobalDyadic
        (AdjoinRoot.mk cubicPolynomial128
          (p.map (Int.castRingHom (ZMod 128)))) =
      Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)
        (Polynomial.aeval coefficientInteger p) := by
  rw [cubicToGlobalDyadic, AdjoinRoot.lift_mk, Polynomial.eval₂_map,
    coefficientBaseMod128_comp_intCast]
  exact (Polynomial.hom_eval₂ p
    (algebraMap ℤ (𝓞 Q.K))
    (Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7))
    coefficientInteger).symm

theorem cubicToGlobalDyadic_surjective :
    Function.Surjective cubicToGlobalDyadic := by
  intro y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h81x : (81 : 𝓞 Q.K) * x ∈
      Algebra.adjoin ℤ {coefficientInteger} :=
    (mem_conductor_iff.mp coefficient_discriminant_mem_conductor) x
  obtain ⟨p, hp⟩ :=
    Algebra.adjoin_mem_exists_aeval ℤ coefficientInteger h81x
  refine ⟨AdjoinRoot.mk cubicPolynomial128
    ((C (49 : ℤ) * p).map (Int.castRingHom (ZMod 128))), ?_⟩
  rw [cubicToGlobalDyadic_mk_map_int]
  apply Ideal.Quotient.eq.mpr
  rw [coefficientPrimeTwo_pow_seven, Ideal.mem_span_singleton]
  refine ⟨31 * x, ?_⟩
  simp only [aeval_mul, aeval_C, hp]
  norm_num
  ring

private theorem cubicPolynomial128_monic' : cubicPolynomial128.Monic := by
  simp only [cubicPolynomial128]
  monicity <;> norm_num

private theorem cubicPolynomial128_natDegree' :
    cubicPolynomial128.natDegree = 3 := by
  simp only [cubicPolynomial128]
  compute_degree!

private def cubicResiduePowerBasis : PowerBasis (ZMod 128) CubicResidue128 :=
  AdjoinRoot.powerBasis' cubicPolynomial128_monic'

theorem cubicResidue128_card : Nat.card CubicResidue128 = 128 ^ 3 := by
  calc
    Nat.card CubicResidue128 =
        Nat.card (Fin cubicResiduePowerBasis.dim →₀ ZMod 128) :=
      Nat.card_congr cubicResiduePowerBasis.basis.repr.toEquiv
    _ = 128 ^ 3 := by
      simp only [cubicResiduePowerBasis, AdjoinRoot.powerBasis'_dim,
        cubicPolynomial128_natDegree']
      simp

noncomputable instance cubicResidue128_finite : Finite CubicResidue128 :=
  Nat.finite_of_card_ne_zero (by rw [cubicResidue128_card]; norm_num)

theorem coefficientDyadicQuotient_card :
    Nat.card CoefficientDyadicQuotient = 128 ^ 3 := by
  rw [← Submodule.cardQuot_apply, ← Ideal.absNorm_apply,
    coefficientPrimeTwo_pow_seven]
  calc
    Ideal.absNorm (Ideal.span {(128 : 𝓞 Q.K)}) =
        128 ^ Module.finrank ℤ (𝓞 Q.K) :=
      Ideal.absNorm_span_natCast 128
    _ = 128 ^ 3 := by
      rw [RingOfIntegers.rank, _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank,
        _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim]



theorem cubicToGlobalDyadic_bijective :
    Function.Bijective cubicToGlobalDyadic :=
  (Nat.bijective_iff_surjective_and_card cubicToGlobalDyadic).2
    ⟨cubicToGlobalDyadic_surjective, by
      rw [cubicResidue128_card, coefficientDyadicQuotient_card]⟩

/-- The actual seventh-power quotient of the coefficient field is the
explicit cubic residue ring used by the finite local certificate. -/
noncomputable def cubicResidue128EquivGlobal :
    CubicResidue128 ≃+* CoefficientDyadicQuotient :=
  RingEquiv.ofBijective cubicToGlobalDyadic cubicToGlobalDyadic_bijective

@[simp] theorem cubicResidue128EquivGlobal_root :
    cubicResidue128EquivGlobal (AdjoinRoot.root cubicPolynomial128) =
      coefficientTauMod128 := by
  exact cubicToGlobalDyadic_root

/-- Genuine reduction from the integer ring of the coefficient-field
completion to the explicit cubic ring modulo `2⁷`. -/
noncomputable def completionReduction :
    coefficientPrimeTwo.adicCompletionIntegers Q.K →+* CubicResidue128 :=
  cubicResidue128EquivGlobal.symm.toRingHom.comp
    ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm.toRingHom.comp
      (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal
          (coefficientPrimeTwo.adicCompletionIntegers Q.K) ^ 7)))



theorem completionReduction_coefficientInteger :
    completionReduction
        (algebraMap (𝓞 Q.K)
          (coefficientPrimeTwo.adicCompletionIntegers Q.K)
          coefficientInteger) =
      AdjoinRoot.root cubicPolynomial128 := by
  apply cubicResidue128EquivGlobal.injective
  rw [cubicResidue128EquivGlobal_root]
  calc
    cubicResidue128EquivGlobal
        (completionReduction
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K)
            coefficientInteger)) =
      (completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) ^ 7)
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K)
            coefficientInteger)) := by
        change cubicResidue128EquivGlobal
          (cubicResidue128EquivGlobal.symm _) = _
        exact RingEquiv.apply_symm_apply _ _
    _ = Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7)
        coefficientInteger := by
      rw [← completionQuotientEquiv_mk]
      exact RingEquiv.symm_apply_apply _ _
    _ = coefficientTauMod128 := rfl

/-! ## The selected simple root of the local two-division cubic -/





































/-! ## The unramified dyadic uniformizer and square lifting -/













/-! ## The normalized projected curve over the integer ring -/



























/-! ## Passage to the completion field -/























/-! ## Projection of the genuine relative descent algebra -/























/-! ## The selected factor of the base-changed minimal descent algebra -/











/-! ## The local image of the minimal descent map -/







































end

end MazurTorsion.XOneEighteenDyadicCompletionBridge

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDyadicGeneratorRingCertificate. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Ring realization of the dyadic generator certificate

The finite certificate in `XOneEighteenDyadicCubicCertificate` uses triples
with a custom multiplication.  This file identifies those triples with the
power basis of

`(ZMod 16)[T] / (T³ - 3T - 1)`

and transfers its nonsquare result to the ordinary ring-theoretic
`IsSquare` predicate.
-/

open Polynomial Module

namespace MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate

noncomputable section



/-- The cubic polynomial defining the finite dyadic coefficient ring. -/
def cubicPolynomial16 : Polynomial R :=
  X ^ 3 - 3 * X - 1

/-- The actual cubic residue ring modulo `16`. -/
abbrev CubicRing16 := AdjoinRoot cubicPolynomial16

/-- The distinguished root of `T³ - 3T - 1`. -/
def tau16 : CubicRing16 :=
  AdjoinRoot.root cubicPolynomial16

private theorem cubicPolynomial16_monic : cubicPolynomial16.Monic := by
  simp only [cubicPolynomial16]
  monicity <;> norm_num

private theorem cubicPolynomial16_natDegree :
    cubicPolynomial16.natDegree = 3 := by
  simp only [cubicPolynomial16]
  compute_degree!

/-- The canonical power basis of the cubic residue ring. -/
def cubicPowerBasis16 : PowerBasis R CubicRing16 :=
  AdjoinRoot.powerBasis' cubicPolynomial16_monic

/-- The canonical power basis, reindexed by the literal type `Fin 3`. -/
def cubicBasis16 : Basis (Fin 3) R CubicRing16 :=
  cubicPowerBasis16.basis.reindex
    (finCongr (by
      simpa only [cubicPowerBasis16, AdjoinRoot.powerBasis'_dim] using
        cubicPolynomial16_natDegree))

@[simp]
private theorem cubicBasis16_apply (i : Fin 3) :
    cubicBasis16 i = tau16 ^ (i : ℕ) := by
  rw [cubicBasis16, Basis.reindex_apply,
    cubicPowerBasis16.basis_eq_pow, finCongr_symm_apply_coe]
  rfl

/-- Coefficient vectors and the cubic residue ring are linearly equivalent
via the power basis `1, τ, τ²`. -/
def fromVec : (Fin 3 → R) ≃ₗ[R] CubicRing16 :=
  cubicBasis16.equivFun.symm

@[simp]
theorem fromVec_apply (v : Fin 3 → R) :
    fromVec v =
      algebraMap R CubicRing16 (v 0) +
        algebraMap R CubicRing16 (v 1) * tau16 +
          algebraMap R CubicRing16 (v 2) * tau16 ^ 2 := by
  simp only [fromVec, Basis.equivFun_symm_apply, Fin.sum_univ_three,
    cubicBasis16_apply, Algebra.smul_def]
  norm_num

/-- The defining relation in the cubic residue ring. -/
theorem tau16_cubic : tau16 ^ 3 = 3 * tau16 + 1 := by
  have h : AdjoinRoot.mk cubicPolynomial16 cubicPolynomial16 = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk cubicPolynomial16
    (X ^ 3 - 3 * X - 1 : Polynomial R) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul, map_ofNat, map_one,
    AdjoinRoot.mk_X] at h
  have h' : tau16 ^ 3 - 3 * tau16 - 1 = 0 := by
    simpa only [tau16] using h
  linear_combination h'

private theorem tau16_pow_four : tau16 ^ 4 = 3 * tau16 ^ 2 + tau16 := by
  calc
    tau16 ^ 4 = tau16 * tau16 ^ 3 := by ring
    _ = 3 * tau16 ^ 2 + tau16 := by rw [tau16_cubic]; ring

private theorem encoded_product
    (a b c d e f : R) :
    (algebraMap R CubicRing16 a + algebraMap R CubicRing16 b * tau16 +
        algebraMap R CubicRing16 c * tau16 ^ 2) *
      (algebraMap R CubicRing16 d + algebraMap R CubicRing16 e * tau16 +
        algebraMap R CubicRing16 f * tau16 ^ 2) =
      algebraMap R CubicRing16 (a * d + b * f + c * e) +
        algebraMap R CubicRing16
            (a * e + b * d + 3 * (b * f + c * e) + c * f) * tau16 +
          algebraMap R CubicRing16
              (a * f + b * e + c * d + 3 * c * f) * tau16 ^ 2 := by
  calc
    (algebraMap R CubicRing16 a + algebraMap R CubicRing16 b * tau16 +
          algebraMap R CubicRing16 c * tau16 ^ 2) *
        (algebraMap R CubicRing16 d + algebraMap R CubicRing16 e * tau16 +
          algebraMap R CubicRing16 f * tau16 ^ 2) =
        algebraMap R CubicRing16 a * algebraMap R CubicRing16 d +
          (algebraMap R CubicRing16 a * algebraMap R CubicRing16 e +
            algebraMap R CubicRing16 b * algebraMap R CubicRing16 d) * tau16 +
          (algebraMap R CubicRing16 a * algebraMap R CubicRing16 f +
            algebraMap R CubicRing16 b * algebraMap R CubicRing16 e +
            algebraMap R CubicRing16 c * algebraMap R CubicRing16 d) * tau16 ^ 2 +
          (algebraMap R CubicRing16 b * algebraMap R CubicRing16 f +
            algebraMap R CubicRing16 c * algebraMap R CubicRing16 e) * tau16 ^ 3 +
          algebraMap R CubicRing16 c * algebraMap R CubicRing16 f * tau16 ^ 4 := by
            ring
    _ = algebraMap R CubicRing16 (a * d + b * f + c * e) +
          algebraMap R CubicRing16
              (a * e + b * d + 3 * (b * f + c * e) + c * f) * tau16 +
            algebraMap R CubicRing16
                (a * f + b * e + c * d + 3 * c * f) * tau16 ^ 2 := by
      rw [tau16_cubic, tau16_pow_four]
      simp only [map_add, map_mul, map_ofNat]
      ring

/-- The power-basis equivalence turns the custom coefficient
multiplication into ordinary multiplication in the quotient ring. -/
theorem fromVec_mul (x y : Fin 3 → R) :
    fromVec
        (XOneEighteenDyadicCubicCertificate.mul x y) =
      fromVec x * fromVec y := by
  simp only [fromVec_apply]
  change
    algebraMap R CubicRing16 (x 0 * y 0 + x 1 * y 2 + x 2 * y 1) +
        algebraMap R CubicRing16
            (x 0 * y 1 + x 1 * y 0 + 3 * (x 1 * y 2 + x 2 * y 1) +
              x 2 * y 2) * tau16 +
          algebraMap R CubicRing16
              (x 0 * y 2 + x 1 * y 1 + x 2 * y 0 + 3 * x 2 * y 2) *
            tau16 ^ 2 =
      (algebraMap R CubicRing16 (x 0) +
          algebraMap R CubicRing16 (x 1) * tau16 +
            algebraMap R CubicRing16 (x 2) * tau16 ^ 2) *
        (algebraMap R CubicRing16 (y 0) +
          algebraMap R CubicRing16 (y 1) * tau16 +
            algebraMap R CubicRing16 (y 2) * tau16 ^ 2)
  exact (encoded_product (x 0) (x 1) (x 2) (y 0) (y 1) (y 2)).symm

/-! ## The bounded normalized-relative-cubic certificate -/









@[simp]
theorem fromVec_one :
    fromVec XOneEighteenDyadicGeneratorCertificate.one = 1 := by
  simp [XOneEighteenDyadicGeneratorCertificate.one, fromVec_apply]

/-- Custom powers of a coefficient vector become ordinary powers in the
quotient ring. -/
@[simp]
theorem fromVec_cubicPow (x : Fin 3 → R) (n : ℕ) :
    fromVec (XOneEighteenDyadicGeneratorCertificate.cubicPow x n) =
      fromVec x ^ n := by
  induction n with
  | zero =>
      simp only [XOneEighteenDyadicGeneratorCertificate.cubicPow,
        fromVec_one, pow_zero]
  | succ n ih =>
      rw [XOneEighteenDyadicGeneratorCertificate.cubicPow, fromVec_mul,
        ih, pow_succ]

@[simp]
private theorem fromVec_quadratic_coefficient :
    fromVec ![-3, 0, 1] = tau16 ^ 2 - 3 := by
  simp only [fromVec_apply, AdjoinRoot.algebraMap_eq, Fin.isValue,
    Matrix.cons_val_zero, map_neg, Matrix.cons_val_one, map_zero, zero_mul,
    add_zero, Matrix.cons_val, map_one, one_mul, map_ofNat]
  ring

@[simp]
private theorem fromVec_linear_coefficient :
    fromVec ![4, 1, -2] = -2 * tau16 ^ 2 + tau16 + 4 := by
  simp only [fromVec_apply, AdjoinRoot.algebraMap_eq, Fin.isValue,
    Matrix.cons_val_zero, map_neg, Matrix.cons_val_one, Matrix.cons_val,
    map_one, one_mul, map_ofNat]
  ring

/-- Evaluation of the vector cubic agrees with evaluation of the displayed
cubic in the actual quotient ring. -/
@[simp]
theorem fromVec_normalizedRelativeCubicValue (z : Fin 3 → R) :
    fromVec (normalizedRelativeCubicValue z) =
      fromVec z ^ 3 + (tau16 ^ 2 - 3) * fromVec z ^ 2 +
        (-2 * tau16 ^ 2 + tau16 + 4) * fromVec z - 1 := by
  simp only [normalizedRelativeCubicValue, map_sub, map_add, fromVec_mul,
    fromVec_quadratic_coefficient, fromVec_linear_coefficient,
    fromVec_one]
  ring



/-- Any root of the normalized relative cubic in the actual quotient ring
is the certified reduction `7 + 10τ + τ²`. -/
theorem normalizedRelativeCubic_root_eq (z : CubicRing16)
    (h : z ^ 3 + (tau16 ^ 2 - 3) * z ^ 2 +
      (-2 * tau16 ^ 2 + tau16 + 4) * z - 1 = 0) :
    z = fromVec
      XOneEighteenDyadicGeneratorCertificate.normalizedGenerator := by
  obtain ⟨v, rfl⟩ := fromVec.surjective z
  have himage :
      fromVec (normalizedRelativeCubicValue v) = fromVec 0 := by
    rw [fromVec_normalizedRelativeCubicValue, map_zero]
    exact h
  have hv : normalizedRelativeCubicValue v = 0 :=
    fromVec.injective himage
  exact congrArg fromVec
    ((normalizedRelativeCubicValue_eq_zero_iff v).mp hv)



/-! ## Exact evaluations of the four generator polynomials -/













/-- The first certificate generator is the value of its displayed integer
polynomial at the normalized generator. -/
theorem fromVec_firstGenerator :
    fromVec XOneEighteenDyadicGeneratorCertificate.firstGenerator =
      let z := fromVec
        XOneEighteenDyadicGeneratorCertificate.normalizedGenerator;
      -z ^ 8 + 3 * z ^ 7 - 8 * z ^ 5 + 6 * z ^ 4 +
        8 * z ^ 3 - 7 * z ^ 2 - 3 * z + 3 := by
  dsimp only
  change fromVec
      (-XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 8 +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 7 -
        (8 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 5 +
        (6 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 4 +
        (8 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 -
        (7 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 -
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.normalizedGenerator +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.one) = _
  simp only [map_add, map_sub, map_neg, map_smul, fromVec_cubicPow,
    fromVec_one]
  simp only [Algebra.smul_def, map_ofNat]
  ring

/-- The second certificate generator is the value of its displayed integer
polynomial at the normalized generator. -/
theorem fromVec_secondGenerator :
    fromVec XOneEighteenDyadicGeneratorCertificate.secondGenerator =
      let z := fromVec
        XOneEighteenDyadicGeneratorCertificate.normalizedGenerator;
      -z ^ 6 + 3 * z ^ 5 - z ^ 4 - 4 * z ^ 3 +
        3 * z ^ 2 + 3 * z - 1 := by
  dsimp only
  change fromVec
      (-XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 6 +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 5 -
        XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 4 -
        (4 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 +
        (3 : R) • XOneEighteenDyadicGeneratorCertificate.normalizedGenerator -
        XOneEighteenDyadicGeneratorCertificate.one) = _
  simp only [map_add, map_sub, map_neg, map_smul, fromVec_cubicPow,
    fromVec_one]
  simp only [Algebra.smul_def, map_ofNat]

/-- The third certificate generator is the value of its displayed integer
polynomial at the normalized generator. -/
theorem fromVec_thirdGenerator :
    fromVec XOneEighteenDyadicGeneratorCertificate.thirdGenerator =
      let z := fromVec
        XOneEighteenDyadicGeneratorCertificate.normalizedGenerator;
      -(z ^ 3 - z ^ 2 + 1) *
        (z ^ 5 - 3 * z ^ 4 + z ^ 3 + 4 * z ^ 2 - 3 * z - 4) := by
  dsimp only
  change fromVec
      (-XOneEighteenDyadicCubicCertificate.mul
        (XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 -
          XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 +
          XOneEighteenDyadicGeneratorCertificate.one)
        (XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 5 -
          (3 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 4 +
          XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 +
          (4 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 -
          (3 : R) • XOneEighteenDyadicGeneratorCertificate.normalizedGenerator -
          (4 : R) • XOneEighteenDyadicGeneratorCertificate.one)) = _
  simp only [map_neg, fromVec_mul, map_add, map_sub, map_smul,
    fromVec_cubicPow, fromVec_one]
  simp only [Algebra.smul_def, map_ofNat]
  ring

/-- The fourth certificate generator is the value of its displayed integer
polynomial at the normalized generator. -/
theorem fromVec_fourthGenerator :
    fromVec XOneEighteenDyadicGeneratorCertificate.fourthGenerator =
      let z := fromVec
        XOneEighteenDyadicGeneratorCertificate.normalizedGenerator;
      -(z ^ 3 - 2 * z ^ 2 + z + 1) *
        (z ^ 3 - z ^ 2 - 2 * z - 1) := by
  dsimp only
  change fromVec
      (-XOneEighteenDyadicCubicCertificate.mul
        (XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 -
          (2 : R) • XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 +
          XOneEighteenDyadicGeneratorCertificate.normalizedGenerator +
          XOneEighteenDyadicGeneratorCertificate.one)
        (XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 3 -
          XOneEighteenDyadicGeneratorCertificate.cubicPow
            XOneEighteenDyadicGeneratorCertificate.normalizedGenerator 2 -
          (2 : R) • XOneEighteenDyadicGeneratorCertificate.normalizedGenerator -
          XOneEighteenDyadicGeneratorCertificate.one)) = _
  simp only [map_neg, fromVec_mul, map_add, map_sub, map_smul,
    fromVec_cubicPow, fromVec_one]
  simp only [Algebra.smul_def, map_ofNat]
  ring

/-- A square in the actual quotient ring gives a square coefficient triple
for the custom multiplication used by the finite certificate. -/
theorem certificate_isSquare_of_isSquare (v : Fin 3 → R)
    (hv : IsSquare (fromVec v)) :
    XOneEighteenDyadicCubicCertificate.IsSquare v := by
  rcases hv with ⟨z, hz⟩
  obtain ⟨w, rfl⟩ := fromVec.surjective z
  refine ⟨w 0, w 1, w 2, ?_⟩
  have hw : ![w 0, w 1, w 2] = w := by
    funext i
    fin_cases i <;> rfl
  rw [hw]
  apply fromVec.injective
  rw [fromVec_mul, hz]

/-- Every nonidentity product in the generator certificate is nonsquare in
the actual cubic residue ring modulo `16`. -/
theorem fromVec_maskedProduct_nonsquare (i : Fin 15) :
    ¬ IsSquare
      (fromVec
        (XOneEighteenDyadicGeneratorCertificate.maskedProduct
          (XOneEighteenDyadicGeneratorCertificate.nonzeroMask i))) := by
  intro h
  exact XOneEighteenDyadicGeneratorCertificate.maskedProduct_nonsquare i
    (certificate_isSquare_of_isSquare _ h)

end

end MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenGlobalSelmerBridge. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Global Selmer bookkeeping for the `X₁(18)` two-descent

This module connects the arithmetic of the explicit degree-nine
two-division field to the generic supported-Selmer cardinality package.
The remaining prime and local-image calculations enter through narrow
certificate hypotheses: the theorem below does not assume a Selmer or
Mordell--Weil conclusion.
-/

open IsDedekindDomain NumberField Polynomial

namespace MazurTorsion.XOneEighteenGlobalSelmerBridge

noncomputable section

open EllipticCurves.X18SelmerCardinality
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionExactSignature
open MazurTorsion.XOneEighteenDescentAlgebraEquiv
open MazurTorsion.XOneEighteenCoefficientDyadicSelmer
open MazurTorsion.XOneEighteenSelmerSieve
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes















/-! ## The exact dyadic support -/





/-! ## The minimal model has genuinely dyadic bad support -/



















/-! ## Relative norm and its four checked kernel generators -/







































/-! ## Cardinality from genuine arithmetic certificates -/







/-! ## The actual ambient relative norm -/

























/-! ## The global subgroup consumed by the Selmer sieve -/



/-- The zero mask represents the identity squareclass. -/
theorem kernelRepresentative_zero : kernelRepresentative 0 = 1 := by
  simp [kernelRepresentative]

/-! ## The unique generic descent factor -/











/-! ## Integral-closure transport for the unique factor -/































end

end MazurTorsion.XOneEighteenGlobalSelmerBridge

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDyadicKernelSeparation. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Dyadic separation of the global `X₁(18)` norm-kernel generators

The selected dyadic factor reduces the normalized degree-nine generator to
`7 + 10τ + τ²` modulo `16`.  Consequently the fifteen nonidentity products
of the four global norm-kernel generators have the nonsquare reductions
certified in `XOneEighteenDyadicGeneratorRingCertificate`.

The raw residue products do not separate arbitrary pairs of masks: even
integral representatives can acquire zero divisors modulo `16`.  Pairwise
separation is instead deduced from the abstract exponent-two squareclass
identity and bitwise XOR, after proving that every nonzero mask has
nonidentity local squareclass.
-/

open Polynomial NumberField

namespace MazurTorsion.XOneEighteenDyadicKernelSeparation

noncomputable section

open MazurTorsion.XOneEighteenDyadicCompletionBridge
open MazurTorsion.XOneEighteenDyadicCubicCertificate
open MazurTorsion.XOneEighteenDyadicGeneratorCertificate
open MazurTorsion.XOneEighteenDyadicGeneratorRingCertificate
open MazurTorsion.XOneEighteenDyadicLocalImage
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionTriadicLift

/-! ## Reduction of the genuine completion modulo `16` -/

private def residueBaseReduction16 : ZMod 128 →+* ZMod 16 :=
  ZMod.castHom (by norm_num : 16 ∣ 128) (ZMod 16)

private theorem cubicPolynomial128_map_residueBaseReduction16 :
    cubicPolynomial128.map residueBaseReduction16 = cubicPolynomial16 := by
  norm_num [cubicPolynomial128, cubicPolynomial16, residueBaseReduction16]

/-- Reduction from the explicit cubic ring modulo `128` to the same cubic
ring modulo `16`. -/
def residueReduction16 : CubicResidue128 →+* CubicRing16 :=
  AdjoinRoot.map residueBaseReduction16 cubicPolynomial128 cubicPolynomial16
    (by rw [cubicPolynomial128_map_residueBaseReduction16])

@[simp] theorem residueReduction16_root :
    residueReduction16 (AdjoinRoot.root cubicPolynomial128) = tau16 := by
  exact AdjoinRoot.map_root _ _ _ _

/-- Genuine reduction of the selected coefficient completion's integer
ring to the cubic coefficient ring modulo `16`. -/
def completionReduction16 : CoefficientCompletionIntegers →+* CubicRing16 :=
  residueReduction16.comp completionReduction

@[simp] theorem completionReduction16_coefficientInteger :
    completionReduction16
        (algebraMap (NumberField.RingOfIntegers Q.K)
          CoefficientCompletionIntegers
          coefficientInteger) = tau16 := by
  rw [completionReduction16, RingHom.comp_apply,
    completionReduction_coefficientInteger, residueReduction16_root]

/-! ## The normalized integral generator in the selected completion -/

/-- The integral relative cubic, base changed to the selected completion's
integer ring. -/
def localNormalizedRelativePolynomial :
    Polynomial CoefficientCompletionIntegers :=
  normalizedRelativePolynomialInteger.map
    (algebraMap (NumberField.RingOfIntegers Q.K)
      CoefficientCompletionIntegers)

theorem localNormalizedRelativePolynomial_monic :
    localNormalizedRelativePolynomial.Monic :=
  normalizedRelativePolynomialInteger_monic.map _

private theorem localProjectedNormalized_root :
    Polynomial.aeval (localRelativeProjection normalizedElement)
      localNormalizedRelativePolynomial = 0 := by
  letI : IsScalarTower (NumberField.RingOfIntegers Q.K)
      CoefficientCompletionIntegers CoefficientCompletion :=
    IsScalarTower.of_algebraMap_eq' (by rfl)
  calc
    Polynomial.aeval (localRelativeProjection normalizedElement)
        localNormalizedRelativePolynomial =
      Polynomial.aeval (localRelativeProjection normalizedElement)
        normalizedRelativePolynomialInteger := by
          rw [localNormalizedRelativePolynomial,
            Polynomial.aeval_map_algebraMap]
    _ = Polynomial.aeval (localRelativeProjection normalizedElement)
        (normalizedRelativePolynomialInteger.map
          (algebraMap (NumberField.RingOfIntegers Q.K) Q.K)) := by
          rw [Polynomial.aeval_map_algebraMap]
    _ = Polynomial.aeval (localRelativeProjection normalizedElement)
        normalizedRelativePolynomial := by
          rw [normalizedRelativePolynomialInteger_map]
    _ = localRelativeProjection
        (Polynomial.aeval normalizedElement normalizedRelativePolynomial) :=
      Polynomial.aeval_algHom_apply
        localRelativeProjection normalizedElement _
    _ = 0 := by rw [normalizedElement_relative_root, map_zero]

private theorem localProjectedNormalized_isIntegral :
    IsIntegral CoefficientCompletionIntegers
      (localRelativeProjection normalizedElement) :=
  ⟨localNormalizedRelativePolynomial,
    localNormalizedRelativePolynomial_monic,
    localProjectedNormalized_root⟩

private theorem exists_localProjectedNormalizedInteger :
    ∃ z : CoefficientCompletionIntegers,
      algebraMap CoefficientCompletionIntegers CoefficientCompletion z =
        localRelativeProjection normalizedElement :=
  IsIntegrallyClosed.isIntegral_iff.mp localProjectedNormalized_isIntegral

/-- The integral lift of the projected normalized degree-nine generator. -/
def localProjectedNormalizedInteger : CoefficientCompletionIntegers :=
  Classical.choose exists_localProjectedNormalizedInteger

@[simp] theorem localProjectedNormalizedInteger_coe :
    (localProjectedNormalizedInteger : CoefficientCompletion) =
      localRelativeProjection normalizedElement :=
  Classical.choose_spec exists_localProjectedNormalizedInteger

private theorem localProjectedNormalizedInteger_root :
    Polynomial.aeval localProjectedNormalizedInteger
      localNormalizedRelativePolynomial = 0 := by
  apply (Polynomial.aeval_algebraMap_eq_zero_iff_of_injective
    (R := CoefficientCompletionIntegers)
    (A := CoefficientCompletionIntegers)
    (B := CoefficientCompletion)
    (FaithfulSMul.algebraMap_injective
      CoefficientCompletionIntegers CoefficientCompletion)).mp
  change Polynomial.aeval
    (localProjectedNormalizedInteger : CoefficientCompletion)
      localNormalizedRelativePolynomial = 0
  rw [localProjectedNormalizedInteger_coe]
  exact localProjectedNormalized_root

/-- The selected normalized generator reduces to `7 + 10τ + τ²` modulo
`16`. -/
theorem completionReduction16_localProjectedNormalizedInteger :
    completionReduction16 localProjectedNormalizedInteger =
      fromVec normalizedGenerator := by
  have hEval :
      Polynomial.aeval localProjectedNormalizedInteger
          normalizedRelativePolynomialInteger = 0 := by
    simpa only [localNormalizedRelativePolynomial,
      Polynomial.aeval_map_algebraMap] using
        localProjectedNormalizedInteger_root
  have h := congrArg completionReduction16 hEval
  have hroot :
      (completionReduction16 localProjectedNormalizedInteger) ^ 3 +
          (tau16 ^ 2 - 3) *
            (completionReduction16 localProjectedNormalizedInteger) ^ 2 +
        (-2 * tau16 ^ 2 + tau16 + 4) *
            completionReduction16 localProjectedNormalizedInteger - 1 = 0 := by
    simpa only [normalizedRelativePolynomialInteger, aeval_add, aeval_sub,
      aeval_mul, aeval_X_pow, aeval_X, aeval_C, aeval_one, map_add, map_sub,
      map_mul, map_pow, map_neg, map_zero, map_one, map_ofNat,
      completionReduction16_coefficientInteger] using h
  exact normalizedRelativeCubic_root_eq _ hroot

/-! ## Reductions of the four explicit generators -/

private def generatorPolynomial : Fin 4 → Polynomial ℤ
  | 0 => h1PolynomialInt
  | 1 => h2PolynomialInt
  | 2 => h3PolynomialInt
  | 3 => h4PolynomialInt

/-- The four projected global generators, as genuine integers in the
selected coefficient completion. -/
def localProjectedGeneratorInteger (i : Fin 4) :
    CoefficientCompletionIntegers :=
  Polynomial.aeval localProjectedNormalizedInteger
    ((generatorPolynomial i).map
      (algebraMap ℤ CoefficientCompletionIntegers))

private theorem map_aeval_int {A B : Type*} [CommRing A] [CommRing B]
    [Algebra ℤ A] [Algebra ℤ B]
    (f : A →+* B) (x : A) (p : Polynomial ℤ) :
    f (Polynomial.aeval x p) = Polynomial.aeval (f x) p := by
  have hA : algebraMap ℤ A = Int.castRingHom A := Subsingleton.elim _ _
  have hB : algebraMap ℤ B = Int.castRingHom B := Subsingleton.elim _ _
  have hcomp : f.comp (Int.castRingHom A) = Int.castRingHom B :=
    Subsingleton.elim _ _
  rw [Polynomial.aeval_def, Polynomial.aeval_def, hA, hB,
    Polynomial.hom_eval₂, hcomp]

private theorem localProjectedInteger_aeval_coe (p : Polynomial ℤ) :
    ((Polynomial.aeval localProjectedNormalizedInteger
        (p.map (algebraMap ℤ CoefficientCompletionIntegers)) :
          CoefficientCompletionIntegers) : CoefficientCompletion) =
      localRelativeProjection (Polynomial.aeval normalizedElement p) := by
  calc
    ((Polynomial.aeval localProjectedNormalizedInteger
        (p.map (algebraMap ℤ CoefficientCompletionIntegers)) :
          CoefficientCompletionIntegers) : CoefficientCompletion) =
      ((Polynomial.aeval localProjectedNormalizedInteger p :
          CoefficientCompletionIntegers) : CoefficientCompletion) := by
        exact congrArg
          (fun x : CoefficientCompletionIntegers ↦
            (x : CoefficientCompletion))
          (Polynomial.aeval_map_algebraMap
            CoefficientCompletionIntegers
            localProjectedNormalizedInteger p)
    _ = Polynomial.aeval
        (localProjectedNormalizedInteger : CoefficientCompletion) p :=
      map_aeval_int
        (algebraMap CoefficientCompletionIntegers CoefficientCompletion)
        localProjectedNormalizedInteger p
    _ = Polynomial.aeval
        (localRelativeProjection normalizedElement) p := by
      rw [localProjectedNormalizedInteger_coe]
    _ = localRelativeProjection
        (Polynomial.aeval normalizedElement p) :=
      (map_aeval_int localRelativeProjection.toRingHom
        normalizedElement p).symm

@[simp] theorem localProjectedGeneratorInteger_coe (i : Fin 4) :
    (localProjectedGeneratorInteger i : CoefficientCompletion) =
      localRelativeProjection
        (match i with
        | 0 => h1
        | 1 => h2
        | 2 => h3
        | 3 => h4) := by
  fin_cases i
  · simpa only [localProjectedGeneratorInteger, generatorPolynomial,
      h1_formula] using localProjectedInteger_aeval_coe h1PolynomialInt
  · simpa only [localProjectedGeneratorInteger, generatorPolynomial,
      h2_formula] using localProjectedInteger_aeval_coe h2PolynomialInt
  · simpa only [localProjectedGeneratorInteger, generatorPolynomial,
      h3_formula] using localProjectedInteger_aeval_coe h3PolynomialInt
  · simpa only [localProjectedGeneratorInteger, generatorPolynomial,
      h4_formula] using localProjectedInteger_aeval_coe h4PolynomialInt

@[simp] theorem completionReduction16_localProjectedGeneratorInteger
    (i : Fin 4) :
    completionReduction16 (localProjectedGeneratorInteger i) =
      fromVec (generator i) := by
  have hmap (p : Polynomial ℤ) :
      completionReduction16
          (Polynomial.aeval localProjectedNormalizedInteger
            (p.map (algebraMap ℤ CoefficientCompletionIntegers))) =
        Polynomial.aeval (fromVec normalizedGenerator) p := by
    calc
      completionReduction16
          (Polynomial.aeval localProjectedNormalizedInteger
            (p.map (algebraMap ℤ CoefficientCompletionIntegers))) =
        completionReduction16
          (Polynomial.aeval localProjectedNormalizedInteger p) := by
            exact congrArg completionReduction16
              (Polynomial.aeval_map_algebraMap
                CoefficientCompletionIntegers
                localProjectedNormalizedInteger p)
      _ = Polynomial.aeval
          (completionReduction16 localProjectedNormalizedInteger) p :=
        map_aeval_int completionReduction16
          localProjectedNormalizedInteger p
      _ = Polynomial.aeval (fromVec normalizedGenerator) p := by
        rw [completionReduction16_localProjectedNormalizedInteger]
  fin_cases i
  · change completionReduction16
      (Polynomial.aeval localProjectedNormalizedInteger
        (h1PolynomialInt.map
          (algebraMap ℤ CoefficientCompletionIntegers))) =
      fromVec XOneEighteenDyadicGeneratorCertificate.firstGenerator
    rw [hmap]
    simpa only [h1PolynomialInt, aeval_add, aeval_sub, aeval_mul,
      aeval_neg, aeval_X_pow, aeval_X, aeval_one, aeval_natCast,
      map_ofNat] using
      fromVec_firstGenerator.symm
  · change completionReduction16
      (Polynomial.aeval localProjectedNormalizedInteger
        (h2PolynomialInt.map
          (algebraMap ℤ CoefficientCompletionIntegers))) =
      fromVec XOneEighteenDyadicGeneratorCertificate.secondGenerator
    rw [hmap]
    simpa only [h2PolynomialInt, aeval_add, aeval_sub, aeval_mul,
      aeval_neg, aeval_X_pow, aeval_X, aeval_one, aeval_natCast,
      map_ofNat] using
      fromVec_secondGenerator.symm
  · change completionReduction16
      (Polynomial.aeval localProjectedNormalizedInteger
        (h3PolynomialInt.map
          (algebraMap ℤ CoefficientCompletionIntegers))) =
      fromVec XOneEighteenDyadicGeneratorCertificate.thirdGenerator
    rw [hmap]
    simpa only [h3PolynomialInt, aeval_add, aeval_sub, aeval_mul,
      aeval_neg, aeval_X_pow, aeval_X, aeval_one, aeval_natCast,
      map_ofNat] using
      fromVec_thirdGenerator.symm
  · change completionReduction16
      (Polynomial.aeval localProjectedNormalizedInteger
        (h4PolynomialInt.map
          (algebraMap ℤ CoefficientCompletionIntegers))) =
      fromVec XOneEighteenDyadicGeneratorCertificate.fourthGenerator
    rw [hmap]
    simpa only [h4PolynomialInt, aeval_add, aeval_sub, aeval_mul,
      aeval_neg, aeval_X_pow, aeval_X, aeval_one, aeval_natCast,
      map_ofNat] using
      fromVec_fourthGenerator.symm

private theorem localProjectedGeneratorInteger_ne_zero (i : Fin 4) :
    (localProjectedGeneratorInteger i : CoefficientCompletion) ≠ 0 := by
  intro hi
  have hiInt : localProjectedGeneratorInteger i = 0 := by
    apply Subtype.ext
    exact hi
  have hred := congrArg completionReduction16 hiInt
  rw [completionReduction16_localProjectedGeneratorInteger, map_zero] at hred
  have hgen : generator i = (0 : Fin 3 → ZMod 16) := by
    apply fromVec.injective
    simpa only [map_zero] using hred
  have hgen_ne : generator i ≠ (0 : Fin 3 → ZMod 16) := by
    rw [generator_eq]
    fin_cases i <;> decide
  exact hgen_ne hgen

private def localProjectedGeneratorUnit (i : Fin 4) :
    CoefficientCompletionˣ :=
  Units.mk0 (localProjectedGeneratorInteger i : CoefficientCompletion)
    (localProjectedGeneratorInteger_ne_zero i)

private theorem localRelativeSquareclassProjection_kernelGenerator
    (i : Fin 4) :
    localRelativeSquareclassProjection (kernelGenerator i) =
      QuotientGroup.mk (localProjectedGeneratorUnit i) := by
  fin_cases i
  · simp only [kernelGenerator, fieldSquareclass,
      localRelativeSquareclassProjection, Units.modPow.map_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    change localRelativeProjection h1 =
      (localProjectedGeneratorInteger 0 : CoefficientCompletion)
    exact (localProjectedGeneratorInteger_coe 0).symm
  · simp only [kernelGenerator, fieldSquareclass,
      localRelativeSquareclassProjection, Units.modPow.map_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    change localRelativeProjection h2 =
      (localProjectedGeneratorInteger 1 : CoefficientCompletion)
    exact (localProjectedGeneratorInteger_coe 1).symm
  · simp only [kernelGenerator, fieldSquareclass,
      localRelativeSquareclassProjection, Units.modPow.map_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    change localRelativeProjection h3 =
      (localProjectedGeneratorInteger 2 : CoefficientCompletion)
    exact (localProjectedGeneratorInteger_coe 2).symm
  · simp only [kernelGenerator, fieldSquareclass,
      localRelativeSquareclassProjection, Units.modPow.map_mk]
    apply congrArg QuotientGroup.mk
    apply Units.ext
    change localRelativeProjection h4 =
      (localProjectedGeneratorInteger 3 : CoefficientCompletion)
    exact (localProjectedGeneratorInteger_coe 3).symm

private def localProjectedRepresentativeInteger (mask : Fin 16) :
    CoefficientCompletionIntegers :=
  (if mask.val.testBit 0 then localProjectedGeneratorInteger 0 else 1) *
  (if mask.val.testBit 1 then localProjectedGeneratorInteger 1 else 1) *
  (if mask.val.testBit 2 then localProjectedGeneratorInteger 2 else 1) *
  (if mask.val.testBit 3 then localProjectedGeneratorInteger 3 else 1)

private def localProjectedRepresentativeUnit (mask : Fin 16) :
    CoefficientCompletionˣ :=
  (if mask.val.testBit 0 then localProjectedGeneratorUnit 0 else 1) *
  (if mask.val.testBit 1 then localProjectedGeneratorUnit 1 else 1) *
  (if mask.val.testBit 2 then localProjectedGeneratorUnit 2 else 1) *
  (if mask.val.testBit 3 then localProjectedGeneratorUnit 3 else 1)

private theorem localProjectedRepresentativeUnit_val (mask : Fin 16) :
    (localProjectedRepresentativeUnit mask : CoefficientCompletion) =
      (localProjectedRepresentativeInteger mask : CoefficientCompletion) := by
  unfold localProjectedRepresentativeUnit localProjectedRepresentativeInteger
  split_ifs <;> rfl

private theorem completionReduction16_localProjectedRepresentativeInteger
    (mask : Fin 16) :
    completionReduction16 (localProjectedRepresentativeInteger mask) =
      fromVec (maskedProduct mask) := by
  unfold localProjectedRepresentativeInteger maskedProduct
  split_ifs <;>
    simp only [map_mul, map_one,
      completionReduction16_localProjectedGeneratorInteger,
      fromVec_mul, fromVec_one, mul_assoc, mul_one, one_mul]

private theorem localRelativeSquareclassProjection_kernelRepresentative
    (mask : Fin 16) :
    localRelativeSquareclassProjection (kernelRepresentative mask) =
      QuotientGroup.mk (localProjectedRepresentativeUnit mask) := by
  unfold kernelRepresentative localProjectedRepresentativeUnit
  split_ifs <;>
    simp only [map_mul, map_one, QuotientGroup.mk_mul, QuotientGroup.mk_one,
      localRelativeSquareclassProjection_kernelGenerator]

private theorem completionReduction16_isSquare_of_field_isSquare
    (x : CoefficientCompletionIntegers)
    (hx : IsSquare (x : CoefficientCompletion)) :
    IsSquare (completionReduction16 x) := by
  obtain ⟨z, hz⟩ := hx
  have hzIntegral : IsIntegral CoefficientCompletionIntegers z := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [pow_two, ← hz]
    exact isIntegral_algebraMap
  obtain ⟨zInt, hzInt⟩ :=
    IsIntegrallyClosed.isIntegral_iff.mp hzIntegral
  refine ⟨completionReduction16 zInt, ?_⟩
  rw [← map_mul]
  apply congrArg completionReduction16
  apply Subtype.ext
  have hzInt' : (zInt : CoefficientCompletion) = z := hzInt
  change (x : CoefficientCompletion) =
    (zInt : CoefficientCompletion) * zInt
  exact hz.trans (congrArg₂ (· * ·) hzInt'.symm hzInt'.symm)

private theorem exists_nonzeroMask_index {mask : Fin 16} (hmask : mask ≠ 0) :
    ∃ i : Fin 15, nonzeroMask i = mask := by
  have hval : mask.val ≠ 0 := by
    intro hzero
    apply hmask
    exact Fin.ext hzero
  let i : Fin 15 := ⟨mask.val - 1, by omega⟩
  refine ⟨i, Fin.ext ?_⟩
  simp only [nonzeroMask, i]
  omega

/-- A global masked product has trivial selected local squareclass exactly
when the mask is zero. -/
theorem localRelativeSquareclassProjection_kernelRepresentative_eq_one_iff
    (mask : Fin 16) :
    localRelativeSquareclassProjection (kernelRepresentative mask) = 1 ↔
      mask = 0 := by
  constructor
  · intro hlocal
    rw [localRelativeSquareclassProjection_kernelRepresentative,
      Units.modPow.mk_eq_one_iff_isSquare] at hlocal
    have hfield :
        IsSquare
          (localProjectedRepresentativeInteger mask : CoefficientCompletion) := by
      simpa only [localProjectedRepresentativeUnit_val] using hlocal
    have hred := completionReduction16_isSquare_of_field_isSquare
      (localProjectedRepresentativeInteger mask) hfield
    rw [completionReduction16_localProjectedRepresentativeInteger] at hred
    by_contra hmask
    obtain ⟨i, hi⟩ := exists_nonzeroMask_index hmask
    rw [← hi] at hred
    exact fromVec_maskedProduct_nonsquare i hred
  · rintro rfl
    rw [kernelRepresentative_zero, map_one]

/-! ## Abstract exponent-two XOR and global injectivity -/









end

end MazurTorsion.XOneEighteenDyadicKernelSeparation

end

theorem solution (mask : Fin 16) :
    MazurTorsion.XOneEighteenDyadicCompletionBridge.localRelativeSquareclassProjection
      (MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative mask) = 1 ↔ mask = 0 := by
  exact MazurTorsion.XOneEighteenDyadicKernelSeparation.localRelativeSquareclassProjection_kernelRepresentative_eq_one_iff mask
#print axioms solution
