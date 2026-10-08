-- Prove2me | solution 1 for MazurTransfer.order18_selected_local_point_image_trivial
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T18:14:10.79732+00:00
-- url     : https://prove2.me/submissions/37886042-d255-4d2e-a9a6-823241af8454

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

/-- A map `f` between groups with `f 1 = 1` that sends triples with product `1` to triples
with product `1` is a homomorphism. Useful when a map is naturally defined via a symmetric
ternary relation, like collinearity on a cubic curve. -/
@[to_additive /-- A map `f` between additive groups with `f 0 = 0` that sends triples with
sum `0` to triples with sum `0` is a homomorphism. Useful when a map is naturally defined via
a symmetric ternary relation, like collinearity on a cubic curve. -/]
def MonoidHom.ofMapMulMulEqOne {f : G → H} (hf₁ : f 1 = 1)
    (hf : ∀ a b c, a * b * c = 1 → f a * f b * f c = 1) :
    G →* H :=
  .ofMapMulInv f fun x y ↦ by
    have (x : G) : f x⁻¹ = (f x)⁻¹ := by
      rw [← mul_eq_one_iff_eq_inv', ← mul_one (_ * _)]
      nth_rewrite 1 [← hf₁]
      exact hf _ _ _ <| by group
    rw [eq_mul_inv_iff_mul_eq, eq_comm, ← inv_mul_eq_one, ← mul_assoc, ← this]
    exact hf _ _ _ <| by group







end Group

section Units

variable {α : Type*} [Monoid α]

@[to_additive]
lemma IsUnit.exists_pow_eq_unit_iff {a : α} (h : IsUnit a) (n : ℕ) :
    (∃ x, x ^ n = h.unit) ↔ ∃ x, x ^ n = a := by
  refine ⟨fun ⟨x, hx⟩ ↦ ⟨x, ?_⟩, fun ⟨x, hx⟩ ↦ ?_⟩
  · simpa using congrArg Units.val hx
  · cases n with
    | zero => exact ⟨1, Units.ext (by simpa using hx)⟩
    | succ _ => exact ⟨(isUnit_pow_succ_iff.mp (hx ▸ h)).unit, Units.ext hx⟩



end Units

section modPow







namespace Units.modPow

variable {α β : Type*} [CommMonoid α] [CommMonoid β] {a b c : α}

open QuotientGroup

lemma unit_eq_one_iff (ha : IsUnit a) (n : ℕ) :
    (ha.unit : Units.modPow α n) = 1 ↔ ∃ z, z ^ n = a := by
  simp [IsUnit.exists_pow_eq_unit_iff]

lemma unit_mul_unit_mul_unit_eq_one_iff (ha : IsUnit a) (hb : IsUnit b) (hc : IsUnit c) (n : ℕ) :
    (ha.unit : Units.modPow α n) * hb.unit * hc.unit = 1 ↔ ∃ z, z ^ n = a * b * c := by
  simp only [← mk_mul, ← IsUnit.unit_mul]
  exact unit_eq_one_iff ((ha.mul hb).mul hc) n

lemma mk_eq_one_iff {u : αˣ} (n : ℕ) :
    (QuotientGroup.mk u : Units.modPow α n) = 1 ↔ ∃ w : αˣ, w ^ n = u := by
  simp





@[simp]
lemma pow_eq_one {n : ℕ} (m : Units.modPow α n) : m ^ n = 1 := by
  obtain ⟨u, rfl⟩ := mk'_surjective _ m
  rw [mk'_apply, ← mk_pow]
  exact (mk_eq_one_iff n).mpr ⟨u, rfl⟩







@[simp]
lemma map_mk (φ : α →* β) (n : ℕ) (u : αˣ) :
    map φ n (QuotientGroup.mk u) = QuotientGroup.mk (Units.map φ u) :=
  rfl





lemma map_unit (φ : α →* β) (n : ℕ) (ha : IsUnit a) :
    map φ n (ha.unit : Units.modPow α n) = ((ha.map φ).unit : Units.modPow β n) := by
  rw [map, ← mk'_apply, map_mk']
  exact congrArg _ (Units.ext rfl)











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


/-- The prime of `R` lying below a prime `w` of an integral extension `B`. -/
def IsDedekindDomain.HeightOneSpectrum.below [Algebra.IsIntegral R B] (w : HeightOneSpectrum B) :
    HeightOneSpectrum R where
  asIdeal := w.asIdeal.under R
  isPrime := Ideal.IsPrime.under R w.asIdeal
  ne_bot := Ideal.IsIntegral.comap_ne_bot R w.ne_bot













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

lemma exists_eq_C_mul_X_sub_C_of_natDegree_le_one {p : R[X]} (hdeg : p.natDegree ≤ 1)
    {x : R} (hx : p.IsRoot x) :
    ∃ γ, p = C γ * (X - C x) := by
  obtain ⟨q, rfl⟩ := dvd_iff_isRoot.mpr hx
  rcases eq_or_ne q 0 with rfl | hq
  · exact ⟨0, by simp⟩
  have h1 : (X - C x).leadingCoeff * q.leadingCoeff ≠ 0 := by
    rwa [(monic_X_sub_C x).leadingCoeff, one_mul, leadingCoeff_ne_zero]
  rw [natDegree_mul' h1, natDegree_X_sub_C] at hdeg
  refine ⟨q.coeff 0, ?_⟩
  nth_rw 1 [eq_C_of_natDegree_eq_zero (by lia : q.natDegree = 0), mul_comm]













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

/-- Evaluation of `AdjoinRoot.map` on the class of a polynomial (the companion of Mathlib's
`AdjoinRoot.map_of` and `AdjoinRoot.map_root`). -/
@[simp]
lemma map_mk {p : R[X]} {q : S[X]} (hq : q ∣ p.map σ) (g : R[X]) :
    AdjoinRoot.map σ p q hq (mk p g) = mk q (g.map σ) := by
  rw [AdjoinRoot.map, lift_mk, ← Polynomial.eval₂_map, ← algebraMap_eq, ← Polynomial.aeval_def,
    aeval_eq]

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

/-- The distinct monic irreducible factors of `f`, as an index type.

Note that this is *not* defined via `normalizedFactors` (which would require `DecidableEq K`);
membership in `normalizedFactors f` is characterized by `Factors.mem_normalizedFactors_iff`. -/
abbrev Factors (f : K[X]) : Type _ := {p : K[X] // p.Monic ∧ Irreducible p ∧ p ∣ f}

namespace Factors

lemma monic (p : f.Factors) : (p : K[X]).Monic := p.2.1

lemma irreducible (p : f.Factors) : Irreducible (p : K[X]) := p.2.2.1

lemma dvd (p : f.Factors) : (p : K[X]) ∣ f := p.2.2.2









lemma separable (hf : f.Separable) (p : f.Factors) : (p : K[X]).Separable :=
  hf.of_dvd p.dvd





















end Factors

end Polynomial

namespace AdjoinRoot

variable {K : Type*} [Field K] {f : K[X]}

instance instFactIrreducible (p : f.Factors) : Fact (Irreducible (p : K[X])) := ⟨p.irreducible⟩

instance instFiniteDimensional (p : f.Factors) : FiniteDimensional K (AdjoinRoot (p : K[X])) :=
  (powerBasis p.irreducible.ne_zero).finite





lemma minpoly_root_factor (p : f.Factors) : minpoly K (root (p : K[X])) = (p : K[X]) := by
  rw [minpoly_root p.irreducible.ne_zero, p.monic.leadingCoeff, inv_one, map_one, mul_one]



open IntermediateField in
/-- If `f` is separable, then each field factor of `K[X]/(f)` is a separable extension of `K`.
This is what `IsIntegralClosure.isDedekindDomain` needs. -/
lemma isSeparable_of_separable (hf : f.Separable) (p : f.Factors) :
    Algebra.IsSeparable K (AdjoinRoot (p : K[X])) := by
  have hsep : IsSeparable K (root (p : K[X])) := by
    rw [IsSeparable, minpoly_root_factor p]
    exact p.separable hf
  have htop : K⟮root (p : K[X])⟯ = ⊤ :=
    adjoin_eq_top_of_algebra (F := K) (S := {root (p : K[X])}) adjoinRoot_eq_top
  have h := (isSeparable_adjoin_simple_iff_isSeparable K (AdjoinRoot (p : K[X]))).2 hsep
  rw [htop] at h
  exact (isSeparable_top (F := K) (E := AdjoinRoot (p : K[X]))).mp h





















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


/- Source module: EllipticCurves.Mathlib.EllipticCurvePoint. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


/-!
# Points of Weierstrass curves over finite fields: decidability and finiteness

Source: MichaelStollBayreuth/EllipticCurves at commit 3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f.
Exact-pin changes are documented in `PORTING.md`.

This file provides `Decidable` instances for the predicates `WeierstrassCurve.Affine.Equation`
and `WeierstrassCurve.Affine.Nonsingular` (over any commutative ring with decidable equality),
and deduces `Finite` and `Fintype` instances for the type `WeierstrassCurve.Affine.Point` of
nonsingular points of a Weierstrass curve over a finite ring, via Mathlib's
`WeierstrassCurve.Affine.nonsingularPointEquiv`.

The decision procedure goes through `equation_iff`/`nonsingular_iff`, so it evaluates the
Weierstrass polynomials directly in the base ring, with no `Polynomial` arithmetic involved.
Consequently, for a concrete curve over `ZMod p` the number of points is computable by `decide`:
`Fintype.card W.Point` enumerates the pairs in `ZMod p × ZMod p` and filters by the (decidable)
nonsingularity condition.

We also provide `WeierstrassCurve.Affine.Point.mapEquiv`, the group *isomorphism* on points
induced by an isomorphism of base fields (the equiv version of
`WeierstrassCurve.Affine.Point.map`); it transports point counts along residue-field
identifications such as `ℤ ⧸ (p) ≃+* ZMod p`.
-/

section

namespace WeierstrassCurve.Affine

variable {R : Type*} [CommRing R] {W' : Affine R}









section PointMap

variable {K : Type*} [Field K] (W : Affine K)

/-- Base change from a field to itself leaves an affine Weierstrass curve unchanged. -/
lemma baseChange_self : (W⁄K).toAffine = W := by
  change W.map (algebraMap K K) = W
  rw [show algebraMap K K = RingHom.id K from Algebra.algebraMap_self]
  exact W.map_id

variable [DecidableEq K]

/-- Transport of points along an equality of Weierstrass curves. -/
def Point.congr {W₁ W₂ : Affine K} (h : W₁ = W₂) : W₁.Point ≃+ W₂.Point := by
  subst h
  exact AddEquiv.refl _

lemma Point.congr_zero {W₁ W₂ : Affine K} (h : W₁ = W₂) :
    Point.congr h (0 : W₁.Point) = 0 := by
  subst h
  rfl

lemma Point.congr_some {W₁ W₂ : Affine K} (h : W₁ = W₂) {x y : K}
    (hp : W₁.Nonsingular x y) :
    Point.congr h (Point.some x y hp) = Point.some x y (h ▸ hp) := by
  subst h
  rfl

variable (L : Type*) [Field L] [Algebra K L] [DecidableEq L]

/-- The base-change homomorphism on points induced by a field extension. -/
noncomputable def pointMap : W.Point →+ (W⁄L).toAffine.Point :=
  (Point.map (W' := W) (Algebra.ofId K L)).comp
    (Point.congr (W.baseChange_self).symm).toAddMonoidHom

lemma pointMap_zero : W.pointMap L 0 = 0 := by
  simp [pointMap, Point.congr_zero]

omit [DecidableEq K] [DecidableEq L] in
/-- Base change preserves nonsingularity, with the target expressed using the canonical
base-changed affine curve. -/
lemma pointMap_nonsingular {x y : K} (h : W.Nonsingular x y) :
    (W⁄L).toAffine.Nonsingular (algebraMap K L x) (algebraMap K L y) := by
  change (W.map (algebraMap K L)).Nonsingular (algebraMap K L x) (algebraMap K L y)
  exact (W.map_nonsingular (algebraMap K L).injective x y).mpr h

lemma pointMap_some {x y : K} (h : W.Nonsingular x y) :
    W.pointMap L (Point.some x y h) =
      Point.some (W' := (W⁄L).toAffine) (algebraMap K L x) (algebraMap K L y)
        (W.pointMap_nonsingular L h) := by
  rw [pointMap, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom, Point.congr_some,
    Point.map_some]
  rfl



end PointMap

namespace Point

variable {S F K : Type*} [CommRing S] [Field F] [Field K] [DecidableEq F] [DecidableEq K]
  [Algebra R S] [Algebra R F] [Algebra S F] [IsScalarTower R S F] [Algebra R K] [Algebra S K]
  [IsScalarTower R S K] (σ : F ≃ₐ[S] K)





end Point

end WeierstrassCurve.Affine

end

end


/- Source module: EllipticCurves.X18WeakMordellWeil. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


section

/-!
# The Weak Mordell-Weil Theorem

The goal of this file is to show that `E(K)/2E(K)` is finite, where `E` is an elliptic curve
given by a Weierstrass equation `y² = x³ + a₂x² + a₄x + a₆ =: f(x)` (so with `a₁ = a₃ = 0`,
which is always achievable when the characteristic is not `2`)
over the fraction field `K` of a Dedekind domain `R`, under finiteness hypotheses — finite
class group and finitely generated unit group for the rings of integers of the field factors
of `K[X]/⟨f⟩` — that are theorems when `K` is a number field.

We use the `x-T` map approach.

The general-purpose material developed along the way, which has nothing to do with elliptic
curves, lives in `EllipticCurves.Mathlib.Basic`.

1. Let `A := K[X]/⟨f(X)⟩` be the étale algebra defined by `f`.
   => done.
2. Define `M := Aˣ⧸squares` and the map `μ : E(K) → M` given by `μ 0 = 1`,
   `μ (x, y) = (x-θ) mod squares` if `f(x) ≠ 0`, else `f'(θ) mod squares`.
   => done (the bare map is defined as `μ₀`).
3. Show that `μ` is a group homomorphism.
   => done.
4. Show that `ker μ = 2E(K)`.
   => done.
5. Show that `im μ` is contained in the kernel of the norm map on square classes.
   => done, via `AdjoinRoot.norm_mk_eq_resultant`, which says that the norm of
   `AdjoinRoot.mk g p` for monic `g` is the resultant of `g` and `p`
   (in `EllipticCurves.Mathlib.Basic`).
   Note that this step is *not* needed for the finiteness result (Steps 6 and 7 do not use
   it); it is included because the norm condition cuts down the Selmer group in explicit
   computations.
6. Show that `im μ ⊆ A(S,2)` for a suitable finite set `S` of "bad" primes.
   => done, as `range_μ_le_selmerGroupA` at the end of the file, for `E` over the fraction field
   of a Dedekind domain and for *any* `S` outside which the coefficients of the cubic are
   integral and `disc f` is a unit. Such sets are provided by `badPrimes` (primes dividing `2`
   or `Δ`, or occurring in a coefficient denominator); the refined sets `discBadPrimes` and
   `badPrimes₂` defined alongside it feed the sharpened Selmer-group bound of
   `EllipticCurves.SelmerGroup`.
7. Show that `A(S,2)` is finite, and conclude that `E(K)/2E(K)` is finite.
   This generic finiteness step is deliberately omitted from this X18 slice. The explicit
   X18 certificate supplies the finite square-class calculation instead; this file stops at
   `range_μ_le_selmerGroupA`.
-/

/-!
### Two commutative-ring identities

These are used in Step 3 (`μ` is a homomorphism); they encode the multiplicativity of the
`x - T` map on the level of coordinates.
-/

section CommRing

variable {R : Type*} [CommRing R]

/-- If `a * b * c = 0`, then `a * b + a * c + b * c` is a square root of the product
of the `b * c - a` and its two analogues. -/
lemma sq_add_add_eq_mul_mul_of_mul_mul_eq_zero {a b c : R} (h : a * b * c = 0) :
    (a * b + a * c + b * c) ^ 2 = (b * c - a) * (a * c - b) * (a * b - c) := by
  linear_combination (a ^ 2 - a * b * c + 2 * a + b ^ 2 + 2 * b + c ^ 2 + 2 * c + 1) * h

/-- If `a * d = 0` and `b * c = d - e ^ 2 * a`, then `d + e * a` is a square root
of `(d - a) * b * c`. -/
lemma sq_add_mul_eq_mul_mul_of_mul_eq_zero {a b c d e : R} (had : a * d = 0)
    (h : b * c = d - e ^ 2 * a) : (d + e * a) ^ 2 = (d - a) * b * c := by
  grobner

end CommRing

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)



/-!
### Step 1: define `A`
-/

open Polynomial

/-- The polynomial on the right hand side of a Weierstrass equation with `a₁ = a₃ = 0`. -/
noncomputable abbrev f : K[X] := X ^ 3 + C W.a₂ * X ^ 2 + C W.a₄ * X + C W.a₆

lemma natDegree_f : W.f.natDegree = 3 := by
  simp only [f]
  compute_degree!

lemma monic_f : W.f.Monic := by
  simp only [f]
  monicity!

lemma f_ne_zero : W.f ≠ 0 := W.monic_f.ne_zero











lemma derivative_f : derivative W.f = C 3 * X ^ 2 + C (2 * W.a₂) * X + C W.a₄ := by
  simp [f, C_ofNat]
  ring



lemma separable_f [W.IsElliptic] [W.IsCharNeTwoNF] : W.f.Separable := by
  have hΔ : W.Δ ≠ 0 := W.isUnit_Δ.ne_zero
  rw [separable_def', derivative_f, f]
  refine ⟨C (W.Δ)⁻¹ * (C (288 * W.a₄ - 96 * W.a₂ ^ 2) * X
      + C (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)),
    C (W.Δ)⁻¹ * (C (32 * W.a₂ ^ 2 - 96 * W.a₄) * X ^ 2
      + C (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * X
      + C (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)), ?_⟩
  rw [mul_assoc, mul_assoc (C (W.Δ)⁻¹), ← mul_add]
  refine mul_left_cancel₀ (C_ne_zero.mpr hΔ) ?_
  rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hΔ, Δ_of_isCharNeTwoNF]
  simp only [C_eq_algebraMap]
  algebra



lemma eval_f (x : K) : W.f.eval x = x ^ 3 + W.a₂ * x ^ 2 + W.a₄ * x + W.a₆ := by simp [f]



lemma equation_iff_eval_f_eq_sq [W.IsCharNeTwoNF] (x y : K) :
    W.Equation x y ↔ W.f.eval x = y ^ 2 := by
  rw [equation_iff x y, eq_comm]
  simp [f]





/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] :=
  X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)







lemma eval_fCofactor_self (x : K) :
    (W.fCofactor x).eval x = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
  simp [fCofactor]
  ring

lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp only [fCofactor, f, eval_add, eval_pow, eval_X, eval_mul, eval_C, map_add, map_pow,
    map_mul, add_sub_add_right_eq_sub]
  algebra

lemma f_eq_mul_of_eval_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.f = W.fCofactor x * (X - C x) := by
  simp [fCofactor_mul_eq, hx]





/- Dividing the relation `(r X + s)² ≡ x - X mod (fCofactor x)` by `r²` yields the polynomial
identity certifying that a point with `2`-torsion `x`-coordinate `x` is divisible by `2`
(used in Step 4). -/


lemma fCofactor_eq_of_f_eq {xP xQ xR : K} (hf : W.f = (X - C xP) * (X - C xQ) * (X - C xR)) :
    W.fCofactor xP = (X - C xQ) * (X - C xR) ∧ W.fCofactor xQ = (X - C xP) * (X - C xR) ∧
      W.fCofactor xR = (X - C xP) * (X - C xQ) := by
  have key {u v w : K} (h : W.f = (X - C u) * ((X - C v) * (X - C w))) :
      W.fCofactor u = (X - C v) * (X - C w) := by
    have h₀ : W.f.eval u = 0 := by rw [h]; simp
    refine mul_left_cancel₀ (X_sub_C_ne_zero u) ?_
    rw [← h, W.f_eq_mul_of_eval_eq_zero h₀, mul_comm]
  exact ⟨key <| by rw [hf]; ring, key <| by rw [hf]; ring, key <| by rw [hf]; ring⟩

lemma deriv_f_ne_zero [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := by
  rw [eval_f] at hx
  have := W.Δ_of_isCharNeTwoNF ▸ W.isUnit_Δ |>.ne_zero
  contrapose! this
  linear_combination ((288 * W.a₄ - 96 * W.a₂ ^ 2) * x
      + (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)) * hx
    + ((32 * W.a₂ ^ 2 - 96 * W.a₄) * x ^ 2 + (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * x
      + (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)) * this

/-- The étale algebra associated to a Weierstrass curve with `a₁ = a₃ = 0`. -/
abbrev A : Type _ := AdjoinRoot W.f

lemma finrank_A : Module.finrank K W.A = 3 := by
  rw [(AdjoinRoot.powerBasis W.f_ne_zero).finrank, AdjoinRoot.powerBasis_dim, natDegree_f]





/-- The étale algebra associated to the cofactor of `f`. -/
abbrev A' (x : K) : Type _ := AdjoinRoot (W.fCofactor x)











/-- The Chinese Remainder Theorem isomorphism `K[X]⧸f ≃ K × K[X]/cf`, where `cf` is the cofactor
`f / (X - x)`. -/
noncomputable def equivProdA' [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) :
    W.A ≃+* K × W.A' x :=
  let eA : W.A ≃+* K[X] ⧸ (Ideal.span {X - C x} * Ideal.span {W.fCofactor x}) :=
    Ideal.quotEquivOfEq <| by
      rw [Ideal.span_singleton_mul_span_singleton, mul_comm, ← W.f_eq_mul_of_eval_eq_zero hx]
  have H : IsCoprime (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).mpr <|
      (W.f_eq_mul_of_eval_eq_zero hx ▸ separable_f W).isCoprime.symm
  eA.trans <|
    (Ideal.quotientMulEquivQuotientProd (Ideal.span {X - C x}) (Ideal.span {W.fCofactor x})
      H).trans <|
    RingEquiv.prodCongr (Polynomial.quotientSpanXSubCAlgEquiv x |>.toRingEquiv) (RingEquiv.refl _)

lemma equivProdA'_apply [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) (p : K[X]) :
    W.equivProdA' hx (AdjoinRoot.mk W.f p) = (p.eval x, AdjoinRoot.mk (W.fCofactor x) p) :=
  rfl



lemma isUnit_mk_iff [W.IsElliptic] [W.IsCharNeTwoNF] {x : K} (hx : W.f.eval x = 0) {p : K[X]} :
    IsUnit (AdjoinRoot.mk W.f p) ↔
      IsUnit (p.eval x) ∧ IsUnit (AdjoinRoot.mk (W.fCofactor x) p) := by
  let e := W.equivProdA' hx
  refine ⟨fun H ↦ ?_, fun H ↦ ?_⟩
  · have : IsUnit (e _) := e.toRingHom.isUnit_map H
    rwa [W.equivProdA'_apply hx, Prod.isUnit_iff] at this
  · have : IsUnit (eval x p, AdjoinRoot.mk (W.fCofactor x) p) := by rwa [Prod.isUnit_iff]
    have : IsUnit (e.symm _) := e.symm.toRingHom.isUnit_map this
    convert this
    rw [RingEquiv.eq_symm_apply, W.equivProdA'_apply hx]

variable {W}

lemma isUnit_mk_sub_X_of_eval_f_ne_zero {x : K} (h : W.f.eval x ≠ 0) :
    IsUnit <| AdjoinRoot.mk W.f (C x - X) := by
  refine .of_mul_eq_one (AdjoinRoot.mk W.f (C (W.f.eval x)⁻¹ * W.fCofactor x)) ?_
  rw [← map_mul, mul_left_comm,
    show (1 : W.A) = AdjoinRoot.mk W.f (1 - C (eval x W.f)⁻¹ * W.f) by simp]
  congr 1
  have h1 : (C x - X) * W.fCofactor x = C (W.f.eval x) - W.f := by
    linear_combination -W.fCofactor_mul_eq x
  rw [h1, mul_sub, ← C_mul, inv_mul_cancel₀ h, map_one]

section

variable [W.IsCharNeTwoNF]

lemma y_eq_zero_of_eval_f_eq_zero {x y : K} (h : W.Equation x y) (hf : W.f.eval x = 0) :
    y = 0 := by
  rwa [equation_iff_eval_f_eq_sq, hf, eq_comm, sq_eq_zero_iff] at h

variable [W.IsElliptic]

lemma isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero {x : K} (h : W.f.eval x = 0) :
    IsUnit <| AdjoinRoot.mk W.f <| C x - X + W.fCofactor x := by
  rw [isUnit_mk_iff W h]
  have H₀ : 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ ≠ 0 := deriv_f_ne_zero W h
  have H₁ : eval x (C x - X + W.fCofactor x) = 3 * x ^ 2 + 2 * W.a₂ * x + W.a₄ := by
    rw [eval_add, W.eval_fCofactor_self]; simp
  have H₂ : (AdjoinRoot.mk (W.fCofactor x)) (C x - X + W.fCofactor x) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X) := by
    simp
  rw [H₁, H₂, isUnit_iff_ne_zero]
  refine ⟨H₀, ?_⟩
  let u := AdjoinRoot.mk (W.fCofactor x) <|
    C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))
  rw [isUnit_iff_exists_inv]
  refine ⟨u, ?_⟩
  rw [← map_mul]
  have : (C x - X) * (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (X + C (2 * x + W.a₂))) =
      C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄)⁻¹ * (-W.fCofactor x) + 1 := by
    rw [mul_left_comm]
    apply_fun (C (3 * x ^ 2 + 2 * W.a₂ * x + W.a₄) * ·) using
      mul_right_injective₀ <| C_ne_zero.mpr H₀
    dsimp only
    rw [mul_add _ _ 1]
    simp_rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ H₀, map_one, one_mul, mul_one]
    simp only [C_eq_algebraMap, fCofactor]
    algebra
  rw [this, map_add, map_one, map_mul, map_neg]
  simp




end

/-!
### Step 2: define `M` and `μ` as a plain map `μ₀`
-/

/-- The group of square classes of units of `W.A`. -/
abbrev M : Type _ := Units.modPow W.A 2

/- `inferInstance` succeeds here, but instance search does not find this instance at the use
sites (e.g., for `mul_right_comm` below) unless it is declared. -/
noncomputable instance : CommGroup W.M := inferInstance

lemma M.sq_eq_one (m : W.M) : m ^ 2 = 1 := Units.modPow.pow_eq_one m

lemma M.mul_self (m : W.M) : m * m = 1 := by rw [← sq, sq_eq_one]



variable [DecidableEq K] [W.IsCharNeTwoNF]

section μ₀

variable [W.IsElliptic]

/-- The descent or `x - T` map on `x`-coordinates: it sends `x` to the square class of
`x - T` if `f x ≠ 0`, and to the square class of `f' T` otherwise. -/
noncomputable def μX (x : K) : W.M :=
  if hx : W.f.eval x = 0
    then (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit
    else (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit

@[simp] lemma μX_of_eval_f_eq_zero {x : K} (hx : W.f.eval x = 0) :
    W.μX x = (isUnit_mk_sub_X_add_fCofactor_of_eval_f_eq_zero hx).unit := by
  simp only [μX, dif_pos hx]

@[simp] lemma μX_of_eval_f_ne_zero {x : K} (hx : W.f.eval x ≠ 0) :
    W.μX x = (isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit := by
  simp only [μX, dif_neg hx]

/-- The descent or `x - T` map `μ₀` on the group of points of an affine Weierstrass curve.
This is a plain map; it is upgraded to a group homomorphism `μ` below. -/
noncomputable def μ₀ : W.Point → W.M
  | 0 => 1
  | .some x _ _ => W.μX x

@[simp] lemma μ₀_zero : W.μ₀ 0 = 1 := rfl

@[simp] lemma μ₀_some {x y : K} (h : W.Nonsingular x y) : W.μ₀ (.some x y h) = W.μX x := rfl

end μ₀

/-!
### Step 3: show that `μ` is a homomorphism `Multiplicative W.Point → M`
-/

lemma Point.some_add_some_add_some_eq_zero {xP yP xQ yQ xR yR : K}
    (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) :
    ∃ pol, (X - C xP) * (X - C xQ) * (X - C xR) = W.f - pol ^ 2 ∧ pol.natDegree ≤ 1 := by
  refine ⟨linePolynomial xP yP <| W.slope xP xQ yP yQ, ?_, ?_⟩
  · have hgeneric : ¬(xP = xQ ∧ yP = W.negY xQ yQ) := by
      by_contra H
      simp [add_of_Y_eq H.1 H.2] at hPQR
    have := addPolynomial_slope hP.1 hQ.1 hgeneric |>.symm
    rw [neg_eq_iff_eq_neg] at this
    convert this using 1
    · congr
      rw [add_eq_zero_iff_eq_neg, neg_some, add_some hgeneric] at hPQR
      grind
    · simp [addPolynomial, polynomial]
  · simp only [linePolynomial, natDegree_add_C]
    compute_degree

open Point in
private lemma xQ_ne_xP_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h : W.f.eval xP = 0) :
    xQ ≠ xP := by
  contrapose! hPQR
  rw! [hPQR] at hQ ⊢
  rw! [y_eq_zero_of_eval_f_eq_zero hP.1 h, y_eq_zero_of_eval_f_eq_zero hQ.1 h]
  rw [add_self_of_Y_eq <| by simp, zero_add]
  exact some_ne_zero hR

open Point in
/- If two of three collinear points have distinct `2`-torsion `x`-coordinates, then the line
through them is horizontal, and `f` splits off all three `x`-coordinates. -/
private lemma f_eq_prod_of_eval_f_eq_zero {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP)
    (hQ : W.Nonsingular xQ yQ) (hR : W.Nonsingular xR yR)
    (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0) (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.f = (X - C xP) * (X - C xQ) * (X - C xR) := by
  have hPQ : xQ ≠ xP := xQ_ne_xP_of_eval_f_eq_zero hP hQ hR hPQR h₁
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  have hpol₀ : pol = 0 := by
    refine pol.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' {xP, xQ} (fun x hx ↦ ?_) ?_
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      apply_fun (·.eval x) at hpol
      rcases hx with rfl | rfl <;>
        rw [eval_sub, ‹eval x (f W) = 0›] at hpol <;>
        simpa using hpol
    · grind
  rwa [hpol₀, zero_pow two_ne_zero, sub_zero, eq_comm] at hpol

/- Forward direction of `exists_eq_two_smul_iff`: if `(x, y)` is divisible by `2`, then the
polynomial identity holds, with `ξ` the `x`-coordinate of a halving point. -/


variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point

lemma μ₀_mul_eq_one (P : W.Point) : W.μ₀ P * W.μ₀ (-P) = 1 := by
  match P with
  | 0 => simp
  | .some x y h => rw [Point.neg_some h, μ₀_some, μ₀_some, M.mul_self]

variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero (h₁ : W.f.eval xP = 0)
    (h₂ : W.f.eval xQ = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  have hf := f_eq_prod_of_eval_f_eq_zero hP hQ hR hPQR h₁ h₂
  have h₃ : W.f.eval xR = 0 := by rw [hf]; simp
  obtain ⟨hfcP, hfcQ, hfcR⟩ := W.fCofactor_eq_of_f_eq hf
  rw [μX_of_eval_f_eq_zero h₁, μX_of_eval_f_eq_zero h₂, μX_of_eval_f_eq_zero h₃,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  simp only [hfcP, hfcQ, hfcR,
    show ∀ (a b c : K), C a - X + (X - C b) * (X - C c) =
      (X - C b) * (X - C c) - (X - C a) by intro a b c; ring]
  rw [map_sub, map_sub _ _ (X - C xQ), map_sub _ _ (X - C xR)]
  simp only [map_mul]
  rw [← sq_add_add_eq_mul_mul_of_mul_mul_eq_zero <| by rw [← map_mul, ← map_mul, ← hf]; simp]
  exact ⟨_, rfl⟩

/- The case where only `xP` is a `2`-torsion `x`-coordinate. -/
private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne (h : W.f.eval xP = 0)
    (hQ₀ : W.f.eval xQ ≠ 0) (hR₀ : W.f.eval xR ≠ 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rw [μX_of_eval_f_eq_zero h, μX_of_eval_f_ne_zero hQ₀, μX_of_eval_f_ne_zero hR₀,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  obtain ⟨γ, rfl⟩ : ∃ γ, pol = C γ * (X - C xP) := by
    apply_fun (·.eval xP) at hpol
    rw [eval_sub, h] at hpol
    exact exists_eq_C_mul_X_sub_C_of_natDegree_le_one hpol₁ (by simpa using hpol)
  rw [W.f_eq_mul_of_eval_eq_zero h, mul_assoc, mul_comm (W.fCofactor _),
    show (C γ * (X - C xP)) ^ 2 = (X - C xP) * (C γ ^ 2 * (X - C xP)) by ring, ← mul_sub] at hpol
  replace hpol := mul_left_cancel₀ (X_sub_C_ne_zero xP) hpol
  simp only [← map_mul]
  rw [show (C xP - X + fCofactor W xP) * (C xQ - X) * (C xR - X) =
    (fCofactor W xP - (X - C xP)) * (X - C xQ) * (X - C xR) by ring, map_mul, map_mul, map_sub]
  rw [← sq_add_mul_eq_mul_mul_of_mul_eq_zero (e := AdjoinRoot.mk W.f (C γ)) ?H₁ ?H₂]
  case H₁ =>
    rw [← map_mul, mul_comm, ← f_eq_mul_of_eval_eq_zero W h]
    simp
  case H₂ => simp only [← map_mul, ← map_pow, ← map_sub, hpol]
  exact ⟨_, rfl⟩

private lemma μX_mul_mul_eq_one_of_eval_f_eq_zero (h : W.f.eval xP = 0) :
    W.μX xP * W.μX xQ * W.μX xR = 1 := by
  by_cases hQ₀ : W.f.eval xQ = 0
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hQ hR hPQR h hQ₀
  by_cases hR₀ : W.f.eval xR = 0
  · rw [mul_right_comm]
    rw [add_right_comm] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_eval_f_eq_zero hP hR hQ hPQR h hR₀
  exact μX_mul_mul_eq_one_of_eval_f_eq_zero_of_ne_of_ne hP hQ hR hPQR h hQ₀ hR₀

lemma μX_mul_mul_eq_one : W.μX xP * W.μX xQ * W.μX xR = 1 := by
  rcases eq_or_ne (W.f.eval xP) 0 with HP | HP
  · exact μX_mul_mul_eq_one_of_eval_f_eq_zero hP hQ hR hPQR HP
  rcases eq_or_ne (W.f.eval xQ) 0 with HQ | HQ
  · rw [mul_comm (W.μX xP)]
    rw [add_comm (Point.some xP ..)] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hQ hP hR hPQR HQ
  rcases eq_or_ne (W.f.eval xR) 0 with HR | HR
  · rw [mul_comm, ← mul_assoc]
    rw [add_comm, ← add_assoc] at hPQR
    exact μX_mul_mul_eq_one_of_eval_f_eq_zero hR hP hQ hPQR HR
  rw [μX_of_eval_f_ne_zero HP, μX_of_eval_f_ne_zero HQ, μX_of_eval_f_ne_zero HR,
    Units.modPow.unit_mul_unit_mul_unit_eq_one_iff]
  obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero hP hQ hR hPQR
  simp only [← map_mul, hpol, neg_sub,
    show (C xP - X) * (C xQ - X) * (C xR - X) = -((X - C xP) * (X - C xQ) * (X - C xR))
      by algebra]
  simp

end μ₀_helper_lemmas

lemma μ₀_mul_mul_eq_one_of_add_add_eq_zero {P Q R : W.Point} (hPQR : P + Q + R = 0) :
    μ₀ P * μ₀ Q * μ₀ R = 1 := by
  match P, Q, R with
  | 0, _, _ =>
    rw [zero_add, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, one_mul, hPQR, μ₀_mul_eq_one]
  | .some .., 0, _
  | .some .., .some .., 0 =>
    rw [add_zero, add_eq_zero_iff_eq_neg'] at hPQR
    rw [μ₀_zero, mul_one, hPQR, μ₀_mul_eq_one]
  | .some xP yP hP, .some xQ yQ hQ, .some xR yR hR =>
    simp only [μ₀_some]
    exact μX_mul_mul_eq_one hP hQ hR hPQR

/-- The descent map as a group homomorphism. -/
noncomputable def μ : Multiplicative W.Point →* W.M :=
  .ofMapMulMulEqOne (f := μ₀ ∘ Multiplicative.toAdd) (by simp) fun P' Q' R' ↦ by
    simp_rw [← toAdd_eq_zero, toAdd_mul, Function.comp_apply]
    exact μ₀_mul_mul_eq_one_of_add_add_eq_zero

@[simp]
lemma μ_apply (P : W.Point) : μ (.ofAdd P) = μ₀ P := rfl



/-!
### Step 4: show that `μ` has kernel `2 • W(K)`.
-/

/- Reverse direction of `exists_eq_two_smul_iff`, in terms of the coefficient identities of
the polynomial identity: the point `(ξ, lξ + m)` lies on `W` and doubles to `(x, ±y)`. -/






section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h







end kernel





/-!
### The `2`-torsion of the group of points

In our situation (`a₁ = a₃ = 0`, so `-(x, y) = (x, -y)`), the `2`-torsion consists of the
origin together with the points `(x, 0)` at the roots of `f`; in particular its order is
the number of roots of `f` in `K` plus one.
-/







/-!
### Step 5: show that `im μ` is contained in the kernel of the norm map.

The norm `Algebra.norm K : W.A →* K` sends units to units, hence induces a homomorphism
`normM : W.M →* Units.modPow K 2` on square classes. We must show `normM ∘ μ = 1`.

Writing `f = (X - θ₁) * (X - θ₂) * (X - θ₃)` over a splitting field, the two cases are:

* if `f x ≠ 0`, then `N (x - θ) = ∏ᵢ (x - θᵢ) = f x = y²`, a square;
* if `f x = 0`, then `N (f' θ) = (f' x)²`, again a square.

Both are instances of `AdjoinRoot.norm_mk_eq_resultant`: the norm of `AdjoinRoot.mk g p` for
monic `g` is the resultant of `g` and `p`. See `norm_mk_C_sub_X` and
`norm_mk_C_sub_X_add_fCofactor` in Step 1 above, which deduce them from it by resultant algebra;
in the second case the factorization `f = fCofactor x * (X - C x)` splits the resultant into two
factors, each equal to `(W.fCofactor x).eval x = f' x`.

`AdjoinRoot.norm_mk_eq_resultant` is proved in `EllipticCurves.Mathlib.Basic`; it is a general fact
about
`AdjoinRoot g` for monic `g` and looks worth upstreaming.
-/

section Step5









end Step5

end WeierstrassCurve.Affine

/-!
## Step 6: `im μ ⊆ A(S,2)`

The right level of generality is: `R` a Dedekind domain, `K = Frac R`, and `E/K` given by a
Weierstrass equation with `a₁ = a₃ = 0`. Everything Step 6 needs — a height-one spectrum,
the `v`-adic
valuations, and unique factorization of fractional ideals — is exactly the Dedekind package.
Number fields are *not* needed until Step 7.

`Mathlib.RingTheory.DedekindDomain.SelmerGroup` already defines, for a Dedekind domain `R` with
fraction field `K`, the group `IsDedekindDomain.selmerGroup : Subgroup (Units.modPow K n)`,
namely the classes whose valuation is `≡ 0 mod n` at every `v ∉ S`. Note that its ambient group
is literally our `Units.modPow K n` (that file has it only as a local notation). So the target
`A(S,2)` should be assembled out of `selmerGroup`s, not defined from scratch.

The obstruction is that `A = AdjoinRoot f` is an étale algebra, not a field, so it has no
`HeightOneSpectrum`. The way around this is the decomposition of `A` into a product of fields,
provided by `EllipticCurves.Mathlib.Basic`: as `f` is separable, `AdjoinRoot.equivPiFactors` gives
`A ≃ₐ[K] ((p : W.f.Factors) → AdjoinRoot p)`, a finite product of finite separable field
extensions of `K` indexed by the monic irreducible factors `p` of `f`, and correspondingly
`AdjoinRoot.modPowEquivPiFactors` gives
`W.M = Units.modPow A 2 ≃* ((p : W.f.Factors) → Units.modPow (AdjoinRoot p) 2)`.
Each factor carries `Field`, `Algebra K` and `FiniteDimensional K` instances, and
`Polynomial.Factors.separable` supplies separability.

With that in hand:

* for each factor, `ringOfIntegersFactor R p := integralClosure R (AdjoinRoot p)` is again a
  Dedekind domain (`IsIntegralClosure.isDedekindDomain`, applicable thanks to
  `AdjoinRoot.isSeparable_of_separable`) with fraction field `AdjoinRoot p`, so
  `IsDedekindDomain.selmerGroup` applies to it;
* `A(S,2)` (`selmerGroupA`) is the preimage under the above isomorphism of the product of the
  `selmerGroupFactor R p`, the `2`-Selmer groups relative to the primes above `S`;
* the containment `im μ ⊆ A(S,2)` is checked factor by factor: for `P = (x, y)` and `w` a prime
  of `ringOfIntegersFactor R p` not above `S`, the valuation `w (x - θ)` is even, where `θ` is
  the root of `p`. If `x` has a pole at `w`, the leading term of the cubic dominates and
  `w (x - θ) = w x = w (y / x) ^ 2`. If `x` is `w`-integral, one uses the factorization
  `y ^ 2 = (x - θ) * (x ^ 2 + θ x + θ ^ 2 + a₂ (x + θ) + a₄)` over the factor `K[X]/(p)`
  itself: the cofactor
  is congruent to `f' θ` modulo `x - θ`, and `f' θ` is a `w`-unit because `w ∤ Δ`. So either
  `x - θ` is a `w`-unit, or the cofactor is, and then `w (x - θ) = w y ^ 2`.

Step 7 (finiteness of `A(S,2)`) then reduces to finiteness of the `2`-Selmer group of each
factor, which needs the primes above `S` to be finite in number, the class group of
`ringOfIntegersFactor R p` to be finite, and its unit group to be finitely generated — i.e.
number fields. Mathlib lists finiteness of `selmerGroup` as a TODO.

Note that the valuation computation stays inside the single field factor `K[X]/(p)`; no
splitting field is needed. That `f' θ` is a unit at every good prime
(`valuation_deriv_root_eq_one`) needs exactly that the coefficients of the cubic are integral
and `disc f` is a unit there — which is what `Δ ∈ badPrimes` buys, via the Bézout identity
behind `separable_f`.

All of this is carried out below: `badPrimes` (`S`) and its finiteness,
`AdjoinRoot.isSeparable_of_separable` (so that `IsIntegralClosure.isDedekindDomain` applies to
each factor), `IsDedekindDomain.HeightOneSpectrum.primesAbove` (the `S i`),
`IsDedekindDomain.selmerGroupAbove`, `selmerGroupA` (`A(S,2)`, as a subgroup of `W.M`), and
finally `range_μ_le_selmerGroupA`.
-/

section Cubic

/- Specializations of `Valuation.map_eval_eq_of_one_lt` and `Valuation.le_one_of_root_monic`
from `EllipticCurves.Mathlib.Basic` to the monic cubic `t ^ 3 + a * t ^ 2 + b * t + c`. They are
specific to Weierstrass equations, so they live here rather than in the general-support file. -/

open Polynomial

variable {L Γ : Type*} [CommRing L] [Nontrivial L] [LinearOrderedCommGroupWithZero Γ]
  (ν : Valuation L Γ) {t a b c : L}







end Cubic

namespace WeierstrassCurve.Affine

open IsDedekindDomain Polynomial UniqueFactorizationMonoid

-- Step 6 needs neither `DecidableEq K` (except where the `x - T` map `μX` enters at the very
-- end) nor the group structure on points, so we re-declare the variables rather than
-- inheriting the ones used for Steps 2-5.
variable {K : Type*} [Field K] (W : Affine K)

/- Notation local to Step 6: for a monic irreducible factor `p` of `f`, `𝕃 p` is the field
factor `K[X]/(p)` of `W.A`, `ι p : K →+* 𝕃 p` is the canonical embedding, and `θ p` is the
image of the root `T` of `f` in `𝕃 p`. -/
local notation:max "𝕃" p:max => AdjoinRoot (p : K[X])
local notation:max "ι" p:max => algebraMap K (AdjoinRoot (p : K[X]))
local notation:max "θ" p:max => AdjoinRoot.root (p : K[X])





















section BadPrimes

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  {v : HeightOneSpectrum R}































end BadPrimes

section DerivativeUnit

/- `f'(x)` is a unit at a rational root `x` of `f` whenever the coefficients are integral and
the valuation of `disc f` is `1` or `exp (-1)`: this is the arithmetic input for the
`2`-torsion `x - T` representative, both at good primes and at primes with
`v(disc f) = exp (-1)`. -/







end DerivativeUnit

section RingOfIntegers

variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K]
  [IsFractionRing R K]

/-- The ring of integers of the field factor `K[X]/(p)` over `R`. -/
noncomputable abbrev ringOfIntegersFactor (p : W.f.Factors) : Type _ :=
  integralClosure R (𝕃 p)

/-- The ring of integers of a field factor is a Dedekind domain: it is the integral closure
of `R` in a finite separable extension of the fraction field `K`. -/
instance isDedekindDomain_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsDedekindDomain (W.ringOfIntegersFactor R p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isDedekindDomain R K (𝕃 p) _

/-- A field factor is the fraction field of its ring of integers. -/
instance isFractionRing_ringOfIntegersFactor [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors) :
    IsFractionRing (W.ringOfIntegersFactor R p) (𝕃 p) :=
  have := AdjoinRoot.isSeparable_of_separable (separable_f W) p
  IsIntegralClosure.isFractionRing_of_finite_extension R K (𝕃 p) _

/-- The ring of integers of a field factor is torsion-free over `R`, as `R` embeds into it. -/
instance instIsTorsionFreeRingOfIntegersFactor (p : W.f.Factors) :
    Module.IsTorsionFree R (W.ringOfIntegersFactor R p) := by
  rw [Module.isTorsionFree_iff_algebraMap_injective]
  have hinj : Function.Injective (algebraMap R (𝕃 p)) := by
    rw [IsScalarTower.algebraMap_eq R K (𝕃 p)]
    exact (ι p).injective.comp (IsFractionRing.injective R K)
  exact fun a b hab ↦ hinj (congrArg Subtype.val hab)













variable [W.IsElliptic] [W.IsCharNeTwoNF] (p : W.f.Factors)
  {w : HeightOneSpectrum (W.ringOfIntegersFactor R p)}
  (ha₂ : (w.below R).valuation K W.a₂ ≤ 1) (ha₄ : (w.below R).valuation K W.a₄ ≤ 1)
  (ha₆ : (w.below R).valuation K W.a₆ ≤ 1) (hd : (w.below R).valuation K W.f.discr = 1)
  -- (this is `w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)













end RingOfIntegers

section Core

variable [W.IsElliptic] [W.IsCharNeTwoNF]
  (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (p : W.f.Factors)
  {x y : K} (h : W.Equation x y) (hx : W.f.eval x ≠ 0)
  (u : (AdjoinRoot (p : K[X]))ˣ)
  (hu : (u : AdjoinRoot (p : K[X])) =
    algebraMap K (AdjoinRoot (p : K[X])) x - AdjoinRoot.root (p : K[X]))
  (w : HeightOneSpectrum (W.ringOfIntegersFactor R p))
  (ha₂ : (w.below R).valuation K W.a₂ ≤ 1) (ha₄ : (w.below R).valuation K W.a₄ ≤ 1)
  (ha₆ : (w.below R).valuation K W.a₆ ≤ 1)
  -- (this is `w.valuation (𝕃 p) (3 * θ p ^ 2 + 2 * ι p W.a₂ * θ p + ι p W.a₄) = 1`;
  -- `variable` commands cannot use the local notation)
  (hderiv : w.valuation (AdjoinRoot (p : K[X]))
    (3 * AdjoinRoot.root (p : K[X]) ^ 2
      + 2 * algebraMap K (AdjoinRoot (p : K[X])) W.a₂ * AdjoinRoot.root (p : K[X])
      + algebraMap K (AdjoinRoot (p : K[X])) W.a₄) = 1)

include h hx hu ha₂ ha₄ ha₆







end Core

section Selmer





variable [W.IsElliptic] [W.IsCharNeTwoNF]





variable (R : Type*) [CommRing R] [IsDedekindDomain R] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R))









/-!
#### The arithmetic input

Write `θ` for `AdjoinRoot.root p`, the image of the root `T` in the field factor `K[X]/(p)`,
and `𝓞` for the integral closure of `R` in `K[X]/(p)`, a Dedekind domain by
`isDedekindDomain_ringOfIntegersFactor` (an instance, in the `RingOfIntegers` section above).

The `p`-component of `μX x` is the square class of the reduction mod `p` of the `x - T`
representative, computed by `projFactor_mk_C_sub_X` and
`projFactor_mk_C_sub_X_add_fCofactor` below: it is `x - θ` in the generic case and
`x - θ + fCofactor x` when `x` is a root of `f`.

What has to be shown is that this class lies in the `2`-Selmer group of `K[X]/(p)`, i.e. that
`w (x - θ)` is even for every prime `w` of `𝓞` not lying above a prime of `S`; away from `S`,
the coefficients of the cubic are integral and `disc f` is a unit, by hypothesis.
The two cases are split off as `mem_selmerGroupFactor_of_eval_f_ne_zero` and
`mem_selmerGroupFactor_of_eval_f_eq_zero`.
-/







variable (hSa₂ : ∀ v ∉ S, v.valuation K W.a₂ ≤ 1) (hSa₄ : ∀ v ∉ S, v.valuation K W.a₄ ≤ 1)
  (hSa₆ : ∀ v ∉ S, v.valuation K W.a₆ ≤ 1) (hSd : ∀ v ∉ S, v.valuation K W.f.discr = 1)





section

variable [DecidableEq K]





end

end Selmer

end WeierstrassCurve.Affine

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


/- Source module: EllipticCurves.X18SelmerLocal. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/


section

/-!
# The local two-descent condition used for `X₁(18)`

This is the local, finite-place slice of Michael Stoll's
`EllipticCurves/SelmerGroup.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.  It contains only base change of the
`x - T` descent map and the cardinality formula for its image over an adic completion.
The global semilocal Selmer-group machinery from the source file is deliberately not
imported here.

The declarations concerning point base change are reused from
`EllipticCurves.Mathlib.EllipticCurvePoint`; the rest follows the pinned source proof.
-/

open Polynomial IsDedekindDomain

namespace WeierstrassCurve.Affine

variable {K : Type*} [Field K] (W : Affine K)

section BaseChange

variable {L₀ : Type*} [Field L₀] (σ : K →+* L₀)

lemma map_f : (W.map σ).toAffine.f = W.f.map σ := by
  simp only [f, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul, Polynomial.map_X,
    Polynomial.map_C, map_a₂, map_a₄, map_a₆]

instance [W.IsCharNeTwoNF] : (W.map σ).IsCharNeTwoNF where
  a₁ := by simp [map_a₁]
  a₃ := by simp [map_a₃]

lemma eval_map_f (x : K) : (W.map σ).toAffine.f.eval (σ x) = σ (W.f.eval x) := by
  rw [map_f, Polynomial.eval_map, Polynomial.eval₂_at_apply]

lemma map_fCofactor (x : K) :
    (W.fCofactor x).map σ = (W.map σ).toAffine.fCofactor (σ x) := by
  simp only [fCofactor, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_mul,
    Polynomial.map_X, Polynomial.map_C, map_a₂, map_a₄, map_add, map_mul, map_pow]

variable (L : Type*) [Field L] [Algebra K L]

instance [W.IsCharNeTwoNF] : (W⁄L).IsCharNeTwoNF :=
  inferInstanceAs (W.map (algebraMap K L)).IsCharNeTwoNF

lemma eval_baseChange_f (x : K) :
    (W⁄L).toAffine.f.eval (algebraMap K L x) = algebraMap K L (W.f.eval x) :=
  W.eval_map_f (algebraMap K L) x

lemma baseChange_fCofactor (x : K) :
    (W.fCofactor x).map (algebraMap K L) = (W⁄L).toAffine.fCofactor (algebraMap K L x) :=
  W.map_fCofactor (algebraMap K L) x

lemma baseChange_f : (W⁄L).toAffine.f = W.f.map (algebraMap K L) :=
  W.map_f (algebraMap K L)



/-- Base change of the cubic étale algebra. -/
noncomputable def mapA : W.A →+* (W⁄L).toAffine.A :=
  AdjoinRoot.map (algebraMap K L) W.f (W⁄L).toAffine.f (W.baseChange_f L).dvd

@[simp]
lemma mapA_mk (p : K[X]) :
    W.mapA L (AdjoinRoot.mk W.f p) = AdjoinRoot.mk (W⁄L).toAffine.f (p.map (algebraMap K L)) :=
  AdjoinRoot.map_mk _ _ _

/-- Restriction of square classes to the base-changed cubic étale algebra. -/
noncomputable def localRes : W.M →* Units.modPow (W⁄L).toAffine.A 2 :=
  Units.modPow.map (W.mapA L).toMonoidHom 2



@[simp]
lemma localRes_unit {a : W.A} (ha : IsUnit a) :
    W.localRes L (ha.unit : W.M) =
      ((ha.map (W.mapA L).toMonoidHom).unit : Units.modPow (W⁄L).toAffine.A 2) := by
  rw [localRes, Units.modPow.map_unit]





variable [W.IsElliptic] [W.IsCharNeTwoNF]

instance : (W⁄L).IsElliptic := inferInstanceAs (W.map (algebraMap K L)).IsElliptic

variable [DecidableEq L]





variable [DecidableEq K]

theorem localRes_μX (x : K) :
    W.localRes L (W.μX x) = μX (W := (W⁄L).toAffine) (algebraMap K L x) := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) = 0 := by
      rw [W.eval_baseChange_f, hx, map_zero]
    rw [μX_of_eval_f_eq_zero hxL, μX_of_eval_f_eq_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mapA_mk, Polynomial.map_add,
      Polynomial.map_sub, Polynomial.map_C, Polynomial.map_X, W.baseChange_fCofactor]
  · have hxL : (W⁄L).toAffine.f.eval (algebraMap K L x) ≠ 0 := by
      rw [W.eval_baseChange_f]
      exact fun h0 ↦ hx ((map_eq_zero _).mp h0)
    rw [μX_of_eval_f_ne_zero hxL, μX_of_eval_f_ne_zero hx, localRes_unit]
    refine congrArg _ (Units.ext ?_)
    rw [IsUnit.unit_spec, IsUnit.unit_spec]
    simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, mapA_mk, Polynomial.map_sub,
      Polynomial.map_C, Polynomial.map_X]

/-- Naturality of `x - T` descent under field extension. -/
theorem localRes_comp_μ :
    (W.localRes L).comp (μ (W := W)) =
      (μ (W := (W⁄L).toAffine)).comp (AddMonoidHom.toMultiplicative (W.pointMap L)) := by
  refine MonoidHom.ext fun P' ↦ ?_
  obtain ⟨P, rfl⟩ := Multiplicative.ofAdd.surjective P'
  simp only [MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
    μ_apply]
  cases P with
  | zero =>
      rw [show (Point.zero : W.Point) = 0 from rfl, μ₀_zero, map_one, W.pointMap_zero L,
        μ₀_zero (W := (W⁄L).toAffine)]
  | some x y hP =>
      rw [μ₀_some, W.pointMap_some L hP, μ₀_some (W := (W⁄L).toAffine), W.localRes_μX L x]



end BaseChange

end WeierstrassCurve.Affine

/-!
## A finite-index Euler characteristic

These lemmas are the narrow portion of Stoll's `EllipticCurves/Mathlib/SelmerGroup.lean`
needed by the local cardinality formula.
-/













namespace WeierstrassCurve.Affine

open NumberField

variable {F : Type*} [Field F] [NumberField F] (W : Affine F)

local notation:max "F_[" v "]" => HeightOneSpectrum.adicCompletion F v
local notation:max "𝒪_[" v "]" => HeightOneSpectrum.adicCompletionIntegers F v
local notation:max "𝕎[" v "]" =>
  WeierstrassCurve.toAffine (W⁄(HeightOneSpectrum.adicCompletion F v))



variable [W.IsElliptic] [W.IsCharNeTwoNF]







end WeierstrassCurve.Affine

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



/-- The quotient curve has discriminant `-2`. -/
theorem quotientCurve_discriminant : quotientCurve.Δ = -2 := by
  norm_num [quotientCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  linear_combination
    (-16 * tau ^ 7 - 80 * tau ^ 6 - 103 * tau ^ 5 + 124 * tau ^ 4 +
      483 * tau ^ 3 + 545 * tau ^ 2 + 284 * tau + 61) *
      (tau_cubic)

instance quotientCurve_isElliptic : quotientCurve.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, quotientCurve_discriminant]
  norm_num















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



theorem relativeTwoDivisionZ_cubic :
    relativeTwoDivisionZ ^ 3 - 3 * relativeTwoDivisionZ ^ 2 +
        408 * relativeTwoDivisionZ + 80 = 0 := by
  simp only [relativeTwoDivisionZ]
  linear_combination
    (27 * s ^ 3 - 162 * s ^ 2 + 243 * s + 216) * s_cubic

/-! ## Exact relative norm certificates -/

























end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenQuotientTwoDescentModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# A characteristic-not-two model of the `X₁(18)` elliptic quotient

This file puts the real-cubic elliptic quotient into the form used by the
`x-T` two-descent.  Both coordinate changes are genuine admissible changes
of Weierstrass variables, so the resulting point maps are additive
equivalences rather than equation-only substitutions.

The completed two-division cubic is also identified with the explicit
relative cubic algebra used by the arithmetic certificates.  No
Mordell--Weil or Selmer conclusion is asserted here.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenQuotientTwoDescentModel

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenTwoDivisionArithmetic









/-! ## Admissible point-group equivalences -/





/-- The characteristic-not-two model used by the `x-T` descent. -/
def descentCurve : WeierstrassCurve K :=
  rationalModel.toCharNeTwoNF • rationalModel



/-- The completed-square equation has coefficients
`[0,-3/4,0,51/2,5/4]`. -/
theorem descentCurve_eq :
    descentCurve =
      (⟨0, -(3 : K) / 4, 0, (51 : K) / 2, (5 : K) / 4⟩ :
        WeierstrassCurve K) := by
  ext <;>
    norm_num [descentCurve, rationalModel,
      WeierstrassCurve.toCharNeTwoNF,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]











/-! ## The completed two-division cubic -/

/-- The monic cubic on the right-hand side of the completed-square model. -/
theorem descentCurve_f :
    descentCurve.toAffine.f =
      X ^ 3 - C ((3 : K) / 4) * X ^ 2 +
        C ((51 : K) / 2) * X + C ((5 : K) / 4) := by
  rw [descentCurve_eq]
  change
    X ^ 3 + C (-(3 : K) / 4) * X ^ 2 + C ((51 : K) / 2) * X +
        C ((5 : K) / 4) =
      X ^ 3 - C ((3 : K) / 4) * X ^ 2 + C ((51 : K) / 2) * X +
        C ((5 : K) / 4)
  have hneg : (-(3 : K) / 4) = -((3 : K) / 4) := by ring
  rw [hneg, map_neg]
  ring



/-- The explicit relative element is a root of the completed two-division
cubic. -/
theorem descentRootInM_isRoot :
    Polynomial.IsRoot
      (descentCurve.toAffine.f.map (algebraMap K M)) descentRootInM := by
  rw [Polynomial.IsRoot, descentCurve_f]
  rw [Polynomial.eval_map_algebraMap]
  simp only [aeval_add, aeval_sub, aeval_mul, map_pow, aeval_X,
    aeval_C]
  change
    descentRootInM ^ 3 -
        algebraMap K M ((3 : K) / 4) * descentRootInM ^ 2 +
      algebraMap K M ((51 : K) / 2) * descentRootInM +
        algebraMap K M ((5 : K) / 4) = 0
  have hcube :
      algebraMap K M (1 / 4 : K) ^ 3 =
        algebraMap K M (1 / 64 : K) := by
    rw [← map_pow]
    norm_num
  have hquad :
      algebraMap K M ((3 : K) / 4) *
          algebraMap K M (1 / 4 : K) ^ 2 =
        algebraMap K M (1 / 64 : K) * (3 : M) := by
    calc
      _ = algebraMap K M (((3 : K) / 4) * (1 / 4 : K) ^ 2) := by
        rw [← map_pow, ← map_mul]
      _ = algebraMap K M ((1 / 64 : K) * 3) := by norm_num
      _ = algebraMap K M (1 / 64 : K) * algebraMap K M (3 : K) := by
        rw [map_mul]
      _ = algebraMap K M (1 / 64 : K) * (3 : M) := by
        simp only [map_ofNat]
  have hlinear :
      algebraMap K M ((51 : K) / 2) *
          algebraMap K M (1 / 4 : K) =
        algebraMap K M (1 / 64 : K) * (408 : M) := by
    calc
      _ = algebraMap K M (((51 : K) / 2) * (1 / 4 : K)) := by
        rw [← map_mul]
      _ = algebraMap K M ((1 / 64 : K) * 408) := by norm_num
      _ = algebraMap K M (1 / 64 : K) * algebraMap K M (408 : K) := by
        rw [map_mul]
      _ = algebraMap K M (1 / 64 : K) * (408 : M) := by
        simp only [map_ofNat]
  have hconst :
      algebraMap K M ((5 : K) / 4) =
        algebraMap K M (1 / 64 : K) * (80 : M) := by
    calc
      _ = algebraMap K M ((1 / 64 : K) * 80) := by norm_num
      _ = algebraMap K M (1 / 64 : K) * algebraMap K M (80 : K) := by
        rw [map_mul]
      _ = algebraMap K M (1 / 64 : K) * (80 : M) := by
        simp only [map_ofNat]
  simp only [descentRootInM, mul_pow]
  linear_combination
    relativeTwoDivisionZ ^ 3 * hcube -
      relativeTwoDivisionZ ^ 2 * hquad +
      relativeTwoDivisionZ * hlinear + hconst +
      algebraMap K M (1 / 64 : K) * relativeTwoDivisionZ_cubic

end

end MazurTorsion.XOneEighteenQuotientTwoDescentModel

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

/-- The coefficient cubic over the residue field. -/
def cubicPolynomial2 : Polynomial (ZMod 2) :=
  X ^ 3 - 3 * X - 1

/-- The residue field of the unramified cubic ring. -/
abbrev CubicResidue2 := AdjoinRoot cubicPolynomial2

private theorem cubicPolynomial128_monic : cubicPolynomial128.Monic := by
  simp only [cubicPolynomial128]
  monicity <;> norm_num

private theorem cubicPolynomial128_natDegree :
    cubicPolynomial128.natDegree = 3 := by
  simp only [cubicPolynomial128]
  compute_degree!

private theorem cubicPolynomial2_monic : cubicPolynomial2.Monic := by
  simp only [cubicPolynomial2]
  monicity <;> norm_num

private theorem cubicPolynomial2_irreducible :
    Irreducible cubicPolynomial2 := by
  have hdegree : cubicPolynomial2.natDegree = 3 := by
    simp only [cubicPolynomial2]
    compute_degree!
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    (p := cubicPolynomial2) ?_ ?_
  · rw [hdegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    simp only [cubicPolynomial2, eval_sub, eval_pow, eval_X,
      eval_mul, eval_ofNat, eval_one]
    fin_cases z <;> decide

private instance cubicPolynomial2_irreducibleFact :
    Fact (Irreducible cubicPolynomial2) :=
  ⟨cubicPolynomial2_irreducible⟩

private def reduceBase : ZMod 128 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 128) (ZMod 2)

private theorem cubicPolynomial_map_reduceBase :
    cubicPolynomial128.map reduceBase = cubicPolynomial2 := by
  norm_num [cubicPolynomial128, cubicPolynomial2, reduceBase]

/-- Reduction of the cubic residue ring modulo `2`. -/
def reduce : CubicResidue128 →+* CubicResidue2 :=
  AdjoinRoot.map reduceBase cubicPolynomial128 cubicPolynomial2
    (by rw [cubicPolynomial_map_reduceBase])

@[simp]
private theorem reduce_mk (p : Polynomial (ZMod 128)) :
    reduce (AdjoinRoot.mk cubicPolynomial128 p) =
      AdjoinRoot.mk cubicPolynomial2 (p.map reduceBase) := by
  exact AdjoinRoot.map_mk _ _ _

private theorem reduce_surjective : Function.Surjective reduce := by
  intro z
  obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨q, hq⟩ := Polynomial.map_surjective reduceBase
    (ZMod.castHom_surjective (by norm_num : 2 ∣ 128)) p
  refine ⟨AdjoinRoot.mk cubicPolynomial128 q, ?_⟩
  rw [reduce_mk, hq]

private theorem base_eq_two_mul_of_reduce_eq_zero :
    ∀ a : ZMod 128, reduceBase a = 0 → ∃ b : ZMod 128, a = 2 * b := by
  decide +kernel

private theorem eq_two_mul_of_reduce_eq_zero
    (z : CubicResidue128) (hz : reduce z = 0) :
    ∃ w : CubicResidue128, z = 2 * w := by
  classical
  induction z using AdjoinRoot.induction_on with
  | ih q =>
      let r := q %ₘ cubicPolynomial128
      have hredq :
          AdjoinRoot.mk cubicPolynomial2 (q.map reduceBase) = 0 := by
        simpa only [reduce_mk] using hz
      have hdvd : cubicPolynomial2 ∣ q.map reduceBase :=
        AdjoinRoot.mk_eq_zero.mp hredq
      have hrmap : r.map reduceBase = 0 := by
        dsimp only [r]
        rw [Polynomial.map_modByMonic reduceBase cubicPolynomial128_monic,
          cubicPolynomial_map_reduceBase]
        exact (Polynomial.modByMonic_eq_zero_iff_dvd
          cubicPolynomial2_monic).2 hdvd
      have hcoeff (n : ℕ) : reduceBase (r.coeff n) = 0 := by
        have h := congrArg (fun p : Polynomial (ZMod 2) ↦ p.coeff n) hrmap
        simpa only [coeff_map, coeff_zero] using h
      choose b hb using fun n ↦
        base_eq_two_mul_of_reduce_eq_zero (r.coeff n) (hcoeff n)
      let s : Polynomial (ZMod 128) :=
        ∑ n ∈ r.support, C (b n) * X ^ n
      have hrs : r = C 2 * s := by
        rw [Polynomial.as_sum_support_C_mul_X_pow r]
        simp only [s, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        rw [hb n, map_mul]
        ring
      refine ⟨AdjoinRoot.mk cubicPolynomial128 s, ?_⟩
      calc
        AdjoinRoot.mk cubicPolynomial128 q =
            AdjoinRoot.mk cubicPolynomial128 r := by
              symm
              simpa only [r, AdjoinRoot.modByMonicHom_mk] using
                AdjoinRoot.mk_leftInverse cubicPolynomial128_monic
                  (AdjoinRoot.mk cubicPolynomial128 q)
        _ = AdjoinRoot.mk cubicPolynomial128 (C 2 * s) := by rw [← hrs]
        _ = 2 * AdjoinRoot.mk cubicPolynomial128 s := by
          simp only [map_mul, AdjoinRoot.mk_C]
          rw [map_ofNat]

private theorem algebraMap_ne_zero {a : ZMod 128} (ha : a ≠ 0) :
    algebraMap (ZMod 128) CubicResidue128 a ≠ 0 := by
  rw [AdjoinRoot.algebraMap_eq]
  apply AdjoinRoot.mk_ne_zero_of_natDegree_lt cubicPolynomial128_monic
  · simpa only [C_ne_zero]
  · simp only [natDegree_C, cubicPolynomial128_natDegree]
    norm_num

private theorem isUnit_of_reduce_ne_zero {z : CubicResidue128}
    (hz : reduce z ≠ 0) : IsUnit z := by
  obtain ⟨w, hw⟩ := reduce_surjective ((reduce z)⁻¹ : CubicResidue2)
  have hker : reduce (1 - z * w) = 0 := by
    rw [map_sub, map_one, map_mul, hw]
    exact sub_eq_zero.mpr (mul_inv_cancel₀ hz).symm
  obtain ⟨q, hq⟩ := eq_two_mul_of_reduce_eq_zero (1 - z * w) hker
  have hnil : IsNilpotent (1 - z * w) := by
    refine ⟨7, ?_⟩
    rw [hq]
    calc
      (2 * q) ^ 7 = 128 * q ^ 7 := by ring
      _ = 0 := by
        rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 128]
        have h128 : (128 : ZMod 128) = 0 := by decide
        rw [h128, map_zero, zero_mul]
  have hzw : IsUnit (z * w) := by
    simpa only [sub_sub_cancel] using hnil.isUnit_one_sub
  exact (IsUnit.mul_iff.mp hzw).1

private theorem isUnit_or_eq_two_mul (z : CubicResidue128) :
    IsUnit z ∨ ∃ w : CubicResidue128, z = 2 * w := by
  by_cases hz : reduce z = 0
  · exact Or.inr (eq_two_mul_of_reduce_eq_zero z hz)
  · exact Or.inl (isUnit_of_reduce_ne_zero hz)

private theorem scalar_four_ne_zero : (4 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 4]
  exact algebraMap_ne_zero (by decide)

private theorem scalar_eight_ne_zero : (8 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 8]
  exact algebraMap_ne_zero (by decide)

private theorem scalar_sixteen_ne_zero : (16 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 16]
  exact algebraMap_ne_zero (by decide)

private theorem scalar_thirtytwo_ne_zero : (32 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 32]
  exact algebraMap_ne_zero (by decide)

private theorem scalar_sixtyfour_ne_zero : (64 : CubicResidue128) ≠ 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 64]
  exact algebraMap_ne_zero (by decide)

private theorem eq_zero_of_mul_unit_eq_zero {a u : CubicResidue128}
    (hu : IsUnit u) (h : a * u = 0) : a = 0 := by
  obtain ⟨U, rfl⟩ := hu
  calc
    a = (a * (U : CubicResidue128)) *
        (↑(U⁻¹) : CubicResidue128) := by simp
    _ = 0 := by rw [h, zero_mul]

private theorem not_isUnit_of_mul_eq_zero {a u : CubicResidue128}
    (ha : a ≠ 0) (h : a * u = 0) : ¬ IsUnit u := by
  intro hu
  exact ha (eq_zero_of_mul_unit_eq_zero hu h)

private theorem eq_thirtytwo_mul_of_four_mul_eq_zero
    (z : CubicResidue128) (hz : 4 * z = 0) :
    ∃ w : CubicResidue128, z = 32 * w := by
  have hnz : ¬ IsUnit z :=
    not_isUnit_of_mul_eq_zero scalar_four_ne_zero hz
  obtain ⟨z₁, hz₁⟩ := (isUnit_or_eq_two_mul z).resolve_left hnz
  have h₁ : 8 * z₁ = 0 := by rw [hz₁] at hz; linear_combination hz
  have hnz₁ : ¬ IsUnit z₁ :=
    not_isUnit_of_mul_eq_zero scalar_eight_ne_zero h₁
  obtain ⟨z₂, hz₂⟩ := (isUnit_or_eq_two_mul z₁).resolve_left hnz₁
  have h₂ : 16 * z₂ = 0 := by rw [hz₂] at h₁; linear_combination h₁
  have hnz₂ : ¬ IsUnit z₂ :=
    not_isUnit_of_mul_eq_zero scalar_sixteen_ne_zero h₂
  obtain ⟨z₃, hz₃⟩ := (isUnit_or_eq_two_mul z₂).resolve_left hnz₂
  have h₃ : 32 * z₃ = 0 := by rw [hz₃] at h₂; linear_combination h₂
  have hnz₃ : ¬ IsUnit z₃ :=
    not_isUnit_of_mul_eq_zero scalar_thirtytwo_ne_zero h₃
  obtain ⟨z₄, hz₄⟩ := (isUnit_or_eq_two_mul z₃).resolve_left hnz₃
  have h₄ : 64 * z₄ = 0 := by rw [hz₄] at h₃; linear_combination h₃
  have hnz₄ : ¬ IsUnit z₄ :=
    not_isUnit_of_mul_eq_zero scalar_sixtyfour_ne_zero h₄
  obtain ⟨z₅, hz₅⟩ := (isUnit_or_eq_two_mul z₄).resolve_left hnz₄
  refine ⟨z₅, ?_⟩
  rw [hz₁, hz₂, hz₃, hz₄, hz₅]
  ring

private theorem eq_eight_mul_of_sixteen_mul_eq_zero
    (z : CubicResidue128) (hz : 16 * z = 0) :
    ∃ w : CubicResidue128, z = 8 * w := by
  have hnz : ¬ IsUnit z :=
    not_isUnit_of_mul_eq_zero scalar_sixteen_ne_zero hz
  obtain ⟨z₁, hz₁⟩ := (isUnit_or_eq_two_mul z).resolve_left hnz
  have h₁ : 32 * z₁ = 0 := by rw [hz₁] at hz; linear_combination hz
  have hnz₁ : ¬ IsUnit z₁ :=
    not_isUnit_of_mul_eq_zero scalar_thirtytwo_ne_zero h₁
  obtain ⟨z₂, hz₂⟩ := (isUnit_or_eq_two_mul z₁).resolve_left hnz₁
  have h₂ : 64 * z₂ = 0 := by rw [hz₂] at h₁; linear_combination h₁
  have hnz₂ : ¬ IsUnit z₂ :=
    not_isUnit_of_mul_eq_zero scalar_sixtyfour_ne_zero h₂
  obtain ⟨z₃, hz₃⟩ := (isUnit_or_eq_two_mul z₂).resolve_left hnz₂
  refine ⟨z₃, ?_⟩
  rw [hz₁, hz₂, hz₃]
  ring

private theorem scalar_one_twenty_eight_eq_zero :
    (128 : CubicResidue128) = 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 128]
  have h128 : (128 : ZMod 128) = 0 := by decide
  rw [h128, map_zero]

private theorem reduce_ne_zero_of_isUnit {z : CubicResidue128}
    (hz : IsUnit z) : reduce z ≠ 0 :=
  (hz.map reduce).ne_zero

private theorem reduce_two_eq_zero :
    reduce (2 : CubicResidue128) = 0 := by
  rw [map_ofNat]
  rw [← map_ofNat (algebraMap (ZMod 2) CubicResidue2) 2]
  have htwo : (2 : ZMod 2) = 0 := by decide
  rw [htwo, map_zero]

private theorem reduce_four_eq_zero :
    reduce (4 : CubicResidue128) = 0 := by
  rw [show (4 : CubicResidue128) = 2 * 2 by ring, map_mul,
    reduce_two_eq_zero, zero_mul]

private theorem reduce_eight_eq_zero :
    reduce (8 : CubicResidue128) = 0 := by
  rw [show (8 : CubicResidue128) = 2 * 4 by ring, map_mul,
    reduce_two_eq_zero, zero_mul]

private theorem reduce_thirtytwo_eq_zero :
    reduce (32 : CubicResidue128) = 0 := by
  rw [show (32 : CubicResidue128) = 2 * 16 by ring, map_mul,
    reduce_two_eq_zero, zero_mul]

private theorem isSquare_of_eq_sq_add_eight_mul
    {x z a : CubicResidue128} (hz : IsUnit z)
    (hx : x = z ^ 2 + 8 * a) : IsSquare x := by
  let u₀ : CubicResidue128 := ↑(hz.unit⁻¹)
  have hzu₀ : z * u₀ = 1 := by
    dsimp only [u₀]
    calc
      z * (↑(hz.unit⁻¹) : CubicResidue128) =
          (↑hz.unit : CubicResidue128) *
            (↑(hz.unit⁻¹) : CubicResidue128) := by
              rw [hz.unit_spec]
      _ = 1 := by simp
  let z₁ : CubicResidue128 := z + 4 * a * u₀
  let a₁ : CubicResidue128 := -(a ^ 2 * u₀ ^ 2)
  have hx₁ : x = z₁ ^ 2 + 16 * a₁ := by
    rw [hx]
    dsimp only [z₁, a₁]
    linear_combination -8 * a * hzu₀
  have hz₁ : IsUnit z₁ := by
    apply isUnit_of_reduce_ne_zero
    have hzred := reduce_ne_zero_of_isUnit hz
    dsimp only [z₁]
    simpa only [map_add, map_mul, reduce_four_eq_zero, zero_mul,
      zero_add, add_zero] using hzred
  let u₁ : CubicResidue128 := ↑(hz₁.unit⁻¹)
  have hz₁u₁ : z₁ * u₁ = 1 := by
    dsimp only [u₁]
    calc
      z₁ * (↑(hz₁.unit⁻¹) : CubicResidue128) =
          (↑hz₁.unit : CubicResidue128) *
            (↑(hz₁.unit⁻¹) : CubicResidue128) := by
              rw [hz₁.unit_spec]
      _ = 1 := by simp
  let z₂ : CubicResidue128 := z₁ + 8 * a₁ * u₁
  let a₂ : CubicResidue128 := -(a₁ ^ 2 * u₁ ^ 2)
  have hx₂ : x = z₂ ^ 2 + 64 * a₂ := by
    rw [hx₁]
    dsimp only [z₂, a₂]
    linear_combination -16 * a₁ * hz₁u₁
  have hz₂ : IsUnit z₂ := by
    apply isUnit_of_reduce_ne_zero
    have hz₁red := reduce_ne_zero_of_isUnit hz₁
    dsimp only [z₂]
    simpa only [map_add, map_mul, reduce_eight_eq_zero, zero_mul,
      zero_add, add_zero] using hz₁red
  let u₂ : CubicResidue128 := ↑(hz₂.unit⁻¹)
  have hz₂u₂ : z₂ * u₂ = 1 := by
    dsimp only [u₂]
    calc
      z₂ * (↑(hz₂.unit⁻¹) : CubicResidue128) =
          (↑hz₂.unit : CubicResidue128) *
            (↑(hz₂.unit⁻¹) : CubicResidue128) := by
              rw [hz₂.unit_spec]
      _ = 1 := by simp
  let z₃ : CubicResidue128 := z₂ + 32 * a₂ * u₂
  have hx₃ : x = z₃ ^ 2 := by
    rw [hx₂]
    dsimp only [z₃]
    linear_combination -64 * a₂ * hz₂u₂ -
      8 * a₂ ^ 2 * u₂ ^ 2 * scalar_one_twenty_eight_eq_zero
  exact ⟨z₃, by simpa only [pow_two] using hx₃⟩

private theorem quadratic_factor_eq_square (x : CubicResidue128) :
    x ^ 2 + 62 * x + 65 = (x + 31) ^ 2 := by
  linear_combination -7 * scalar_one_twenty_eight_eq_zero

private theorem eq_two_mul_of_sq_eq_mul_sq_of_eq_two_mul
    {x y t u : CubicResidue128} (hcurve : y ^ 2 = x * t ^ 2)
    (ht : t = 2 * u) :
    ∃ v : CubicResidue128, y = 2 * v := by
  have htred : reduce t = 0 := by
    rw [ht, map_mul, reduce_two_eq_zero, zero_mul]
  have hyredsq : reduce y ^ 2 = 0 := by
    rw [← map_pow, hcurve, map_mul, map_pow, htred]
    ring
  have hyred : reduce y = 0 := sq_eq_zero_iff.mp hyredsq
  exact eq_two_mul_of_reduce_eq_zero y hyred

private theorem isUnit_of_add_thirtyone_eq_two_mul
    {x u : CubicResidue128} (hx : x + 31 = 2 * u) :
    IsUnit x := by
  apply isUnit_of_reduce_ne_zero
  intro hxred
  have hred := congrArg reduce hx
  rw [map_add, hxred, map_mul, reduce_two_eq_zero, zero_mul] at hred
  have hthirtyone : reduce (31 : CubicResidue128) = 1 := by
    rw [show (31 : CubicResidue128) = 1 + 2 * 15 by ring,
      map_add, map_one, map_mul, reduce_two_eq_zero, zero_mul, add_zero]
  rw [hthirtyone, zero_add] at hred
  exact one_ne_zero hred

private theorem isSquare_of_unit_scaled_congruence
    {x v u a : CubicResidue128} (hx : IsUnit x) (hu : IsUnit u)
    (hcong : v ^ 2 - x * u ^ 2 = 8 * a) :
    IsSquare x := by
  let uInv : CubicResidue128 := ↑(hu.unit⁻¹)
  have huuInv : u * uInv = 1 := by
    dsimp only [uInv]
    calc
      u * (↑(hu.unit⁻¹) : CubicResidue128) =
          (↑hu.unit : CubicResidue128) *
            (↑(hu.unit⁻¹) : CubicResidue128) := by
              rw [hu.unit_spec]
      _ = 1 := by simp
  let z : CubicResidue128 := v * uInv
  let b : CubicResidue128 := -(a * uInv ^ 2)
  have hxz : x = z ^ 2 + 8 * b := by
    dsimp only [z, b]
    linear_combination -uInv ^ 2 * hcong -
      x * (u * uInv + 1) * huuInv
  have hz : IsUnit z := by
    apply isUnit_of_reduce_ne_zero
    intro hzred
    have hxred := reduce_ne_zero_of_isUnit hx
    apply hxred
    have hred := congrArg reduce hxz
    rw [map_add, map_pow, hzred, zero_pow (by norm_num : 2 ≠ 0),
      map_mul, reduce_eight_eq_zero, zero_mul, add_zero] at hred
    exact hred
  exact isSquare_of_eq_sq_add_eight_mul hz hxz

private theorem isSquare_of_shift_valuation_one
    {x y u : CubicResidue128}
    (hcurve : y ^ 2 = x * (x + 31) ^ 2)
    (hshift : x + 31 = 2 * u) (hu : IsUnit u) :
    IsSquare x := by
  obtain ⟨v, hv⟩ :=
    eq_two_mul_of_sq_eq_mul_sq_of_eq_two_mul hcurve hshift
  have hfour : 4 * (v ^ 2 - x * u ^ 2) = 0 := by
    rw [hv, hshift] at hcurve
    linear_combination hcurve
  obtain ⟨a, ha⟩ :=
    eq_thirtytwo_mul_of_four_mul_eq_zero
      (v ^ 2 - x * u ^ 2) hfour
  have ha8 : v ^ 2 - x * u ^ 2 = 8 * (4 * a) := by
    rw [ha]
    ring
  exact isSquare_of_unit_scaled_congruence
    (isUnit_of_add_thirtyone_eq_two_mul hshift) hu ha8

private theorem isSquare_of_shift_valuation_two
    {x y u : CubicResidue128}
    (hcurve : y ^ 2 = x * (x + 31) ^ 2)
    (hshift : x + 31 = 4 * u) (hu : IsUnit u) :
    IsSquare x := by
  have hshift2 : x + 31 = 2 * (2 * u) := by rw [hshift]; ring
  obtain ⟨y₁, hy₁⟩ :=
    eq_two_mul_of_sq_eq_mul_sq_of_eq_two_mul hcurve hshift2
  have hfour : 4 * (y₁ ^ 2 - 4 * x * u ^ 2) = 0 := by
    rw [hy₁, hshift] at hcurve
    linear_combination hcurve
  obtain ⟨a₁, ha₁⟩ :=
    eq_thirtytwo_mul_of_four_mul_eq_zero
      (y₁ ^ 2 - 4 * x * u ^ 2) hfour
  have hy₁redsq : reduce y₁ ^ 2 = 0 := by
    have hred := congrArg reduce ha₁
    simpa only [map_sub, map_pow, map_mul, reduce_four_eq_zero,
      reduce_thirtytwo_eq_zero, zero_mul, sub_zero] using hred
  have hy₁red : reduce y₁ = 0 := sq_eq_zero_iff.mp hy₁redsq
  obtain ⟨v, hv⟩ := eq_two_mul_of_reduce_eq_zero y₁ hy₁red
  have hsixteen : 16 * (v ^ 2 - x * u ^ 2) = 0 := by
    rw [hy₁, hv, hshift] at hcurve
    linear_combination hcurve
  obtain ⟨a, ha⟩ :=
    eq_eight_mul_of_sixteen_mul_eq_zero
      (v ^ 2 - x * u ^ 2) hsixteen
  exact isSquare_of_unit_scaled_congruence
    (isUnit_of_add_thirtyone_eq_two_mul hshift2) hu ha

private theorem isSquare_of_shift_divisible_by_eight
    {x u : CubicResidue128} (hshift : x + 31 = 8 * u) :
    IsSquare x := by
  have hx : x = (1 : CubicResidue128) ^ 2 + 8 * (u - 4) := by
    linear_combination hshift
  exact isSquare_of_eq_sq_add_eight_mul isUnit_one hx

/--
Every point of the normalized curve over the unramified cubic quotient
modulo `2⁷` has square first coordinate.  The proof splits according to the
truncated valuation of `X + 31`; it performs no enumeration of residue-ring
pairs.
-/
theorem integral_cubic_mod128 :
    ∀ X Y : CubicResidue128,
      Y ^ 2 = X * (X ^ 2 + 62 * X + 65) → IsSquare X := by
  intro x y hcurve
  have hcurve' : y ^ 2 = x * (x + 31) ^ 2 := by
    rw [← quadratic_factor_eq_square]
    exact hcurve
  rcases isUnit_or_eq_two_mul (x + 31) with hunit | ⟨u, hshift⟩
  · let uInv : CubicResidue128 := ↑(hunit.unit⁻¹)
    have huuInv : (x + 31) * uInv = 1 := by
      dsimp only [uInv]
      calc
        (x + 31) * (↑(hunit.unit⁻¹) : CubicResidue128) =
            (↑hunit.unit : CubicResidue128) *
              (↑(hunit.unit⁻¹) : CubicResidue128) := by
                rw [hunit.unit_spec]
        _ = 1 := by simp
    refine ⟨y * uInv, ?_⟩
    have hroot : x = (y * uInv) ^ 2 := by
      linear_combination -uInv ^ 2 * hcurve' -
        x * ((x + 31) * uInv + 1) * huuInv
    simpa only [pow_two] using hroot
  · rcases isUnit_or_eq_two_mul u with hu | ⟨u₂, hu₂⟩
    · exact isSquare_of_shift_valuation_one hcurve' hshift hu
    · have hshift4 : x + 31 = 4 * u₂ := by rw [hshift, hu₂]; ring
      rcases isUnit_or_eq_two_mul u₂ with hu₂unit | ⟨u₃, hu₃⟩
      · exact isSquare_of_shift_valuation_two hcurve' hshift4 hu₂unit
      · exact isSquare_of_shift_divisible_by_eight (by
          rw [hshift4, hu₃]
          ring)





end

end MazurTorsion.XOneEighteenDyadicLocalImage

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDescentAlgebraEquiv. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Identifying the `X₁(18)` descent algebra with the explicit compositum

The generic `x - T` descent is phrased in the cubic algebra obtained from
the completed two-division polynomial.  The arithmetic certificates use the
explicit relative cubic compositum generated by `s`, with `s³ = 3s + 10`.
This file gives an actual algebra equivalence between those presentations.

The inverse is completely explicit.  If `z` denotes the root of the
completed two-division polynomial, then

`s = (4z² - 11z + 70) / 27`.

Thus no irreducibility or dimension-count oracle is hidden in the bridge.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenDescentAlgebraEquiv

noncomputable section

open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

/-- The completed two-division root generates the explicit relative cubic
field: the original generator is recovered by this quadratic expression. -/
theorem recover_s_in_compositum :
    (4 * descentRootInM ^ 2 - 11 * descentRootInM + 70) / 27 = s := by
  have hquarter : algebraMap K M (1 / 4 : K) = (1 / 4 : M) := by
    simp only [div_eq_mul_inv, one_mul, map_inv₀, map_ofNat]
  simp only [descentRootInM, relativeTwoDivisionZ]
  rw [hquarter]
  field_simp
  linear_combination 9 * (s - 4) * s_cubic

private theorem descentRootInM_adjoin_eq_top :
    IntermediateField.adjoin K {descentRootInM} = ⊤ := by
  let L : IntermediateField K M :=
    IntermediateField.adjoin K {descentRootInM}
  have hz : descentRootInM ∈ L :=
    IntermediateField.mem_adjoin_simple_self K descentRootInM
  have hs : s ∈ L := by
    rw [← recover_s_in_compositum]
    exact L.div_mem
      (L.add_mem
        (L.sub_mem
          (L.mul_mem (L.natCast_mem 4) (L.pow_mem hz 2))
          (L.mul_mem (L.natCast_mem 11) hz))
        (L.natCast_mem 70))
      (L.natCast_mem 27)
  apply top_unique
  intro x _hx
  have hadjoin :
      Algebra.adjoin K ({s} : Set M) ≤
        L.toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hs)
  have hsTop : Algebra.adjoin K ({s} : Set M) = ⊤ := by
    change Algebra.adjoin K
      ({AdjoinRoot.root relativePolynomial} : Set M) = ⊤
    exact AdjoinRoot.adjoinRoot_eq_top
  rw [hsTop] at hadjoin
  change x ∈ L
  exact hadjoin (show x ∈ (⊤ : Subalgebra K M) from trivial)

/-- The completed two-division cubic is irreducible over the real cubic
coefficient field. -/
theorem descentPolynomial_irreducible :
    Irreducible descentCurve.toAffine.f := by
  have hroot : Polynomial.aeval descentRootInM descentCurve.toAffine.f = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    exact descentRootInM_isRoot
  have hdegree : (minpoly K descentRootInM).natDegree = 3 := by
    have h :=
      (Field.primitive_element_iff_minpoly_natDegree_eq
        K descentRootInM).mp descentRootInM_adjoin_eq_top
    simpa only [finrank_M_over_K] using h
  have hint : IsIntegral K descentRootInM := IsIntegral.of_finite K descentRootInM
  have hdvd : minpoly K descentRootInM ∣ descentCurve.toAffine.f :=
    minpoly.dvd K descentRootInM hroot
  have heq : descentCurve.toAffine.f = minpoly K descentRootInM :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hint) descentCurve.toAffine.monic_f hdvd (by
        rw [hdegree, descentCurve.toAffine.natDegree_f])
  rw [heq]
  exact minpoly.irreducible hint

private instance descentPolynomial_irreducibleFact :
    Fact (Irreducible descentCurve.toAffine.f) :=
  ⟨descentPolynomial_irreducible⟩

private theorem descentPolynomial_cleared :
    C (4 : K) * descentCurve.toAffine.f =
      C (4 : K) * X ^ 3 - C (3 : K) * X ^ 2 +
        C (102 : K) * X + C (5 : K) := by
  rw [descentCurve_f, mul_add, mul_add, mul_sub]
  simp only [← mul_assoc, ← C_mul]
  norm_num

/-- The distinguished root in the generic completed two-division algebra. -/
def genericRoot : descentCurve.toAffine.A :=
  AdjoinRoot.root descentCurve.toAffine.f

/-- The generic root satisfies the cleared completed two-division cubic. -/
theorem genericRoot_cubic :
    4 * genericRoot ^ 3 - 3 * genericRoot ^ 2 +
        102 * genericRoot + 5 = 0 := by
  have hroot : Polynomial.aeval genericRoot descentCurve.toAffine.f = 0 := by
    rw [aeval_def]
    exact AdjoinRoot.eval₂_root descentCurve.toAffine.f
  have h := congrArg (Polynomial.aeval genericRoot)
    descentPolynomial_cleared
  simp only [map_mul, map_sub, map_add, map_pow, aeval_X,
    map_ofNat, hroot, mul_zero] at h
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h.symm

/-- Recover the relative generator from the completed two-division root. -/
def recoveredS : descentCurve.toAffine.A :=
  (4 * genericRoot ^ 2 - 11 * genericRoot + 70) / 27

/-- The recovered element satisfies `S³ - 3S - 10`. -/
theorem recoveredS_cubic : recoveredS ^ 3 = 3 * recoveredS + 10 := by
  have h := genericRoot_cubic
  let N : descentCurve.toAffine.A :=
    4 * genericRoot ^ 2 - 11 * genericRoot + 70
  have hN : N ^ 3 - 3 * 27 ^ 2 * N - 10 * 27 ^ 3 = 0 := by
    dsimp only [N]
    linear_combination
      (16 * genericRoot ^ 3 - 120 * genericRoot ^ 2 +
        705 * genericRoot - 1384) * h
  have h27 : (27 : descentCurve.toAffine.A) ≠ 0 := by
    simpa only [map_ofNat] using
      (_root_.map_ne_zero (algebraMap K descentCurve.toAffine.A)).mpr
        (by norm_num : (27 : K) ≠ 0)
  change (N / 27) ^ 3 = 3 * (N / 27) + 10
  field_simp [h27]
  linear_combination hN

private theorem recoveredS_isRoot :
    Polynomial.aeval recoveredS relativePolynomial = 0 := by
  simp only [relativePolynomial, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat]
  linear_combination recoveredS_cubic

/-- Map the generic descent algebra to the explicit relative cubic field. -/
def toCompositumHom : descentCurve.toAffine.A →ₐ[K] M :=
  AdjoinRoot.liftAlgHom descentCurve.toAffine.f (Algebra.ofId K M)
    descentRootInM (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      rw [← Polynomial.eval_map_algebraMap]
      exact descentRootInM_isRoot)

@[simp]
theorem toCompositumHom_genericRoot :
    toCompositumHom genericRoot = descentRootInM := by
  exact AdjoinRoot.liftAlgHom_root descentCurve.toAffine.f _ _ _

/-- Map the explicit relative cubic presentation back to the generic
descent algebra. -/
def fromCompositumHom : M →ₐ[K] descentCurve.toAffine.A :=
  AdjoinRoot.liftAlgHom relativePolynomial
    (Algebra.ofId K descentCurve.toAffine.A) recoveredS (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      exact recoveredS_isRoot)

@[simp]
theorem fromCompositumHom_s : fromCompositumHom s = recoveredS := by
  exact AdjoinRoot.liftAlgHom_root relativePolynomial _ _ _

private theorem recover_genericRoot :
    algebraMap K descentCurve.toAffine.A (1 / 4 : K) *
        (3 * recoveredS ^ 2 - 6 * recoveredS - 5) = genericRoot := by
  have hquarter :
      algebraMap K descentCurve.toAffine.A (1 / 4 : K) =
        (1 / 4 : descentCurve.toAffine.A) := by
    simp only [div_eq_mul_inv, one_mul, map_inv₀, map_ofNat]
  rw [hquarter]
  have h := genericRoot_cubic
  let N : descentCurve.toAffine.A :=
    4 * genericRoot ^ 2 - 11 * genericRoot + 70
  have hN :
      3 * N ^ 2 - 6 * 27 * N - 5 * 27 ^ 2 -
          4 * 27 ^ 2 * genericRoot = 0 := by
    dsimp only [N]
    linear_combination 3 * (4 * genericRoot - 19) * h
  have h4 : (4 : descentCurve.toAffine.A) ≠ 0 := by
    simpa only [map_ofNat] using
      (_root_.map_ne_zero (algebraMap K descentCurve.toAffine.A)).mpr
        (by norm_num : (4 : K) ≠ 0)
  have h27 : (27 : descentCurve.toAffine.A) ≠ 0 := by
    simpa only [map_ofNat] using
      (_root_.map_ne_zero (algebraMap K descentCurve.toAffine.A)).mpr
        (by norm_num : (27 : K) ≠ 0)
  change (1 / 4 : descentCurve.toAffine.A) *
      (3 * (N / 27) ^ 2 - 6 * (N / 27) - 5) = genericRoot
  field_simp [h4, h27]
  linear_combination hN

private theorem to_from :
    toCompositumHom.comp fromCompositumHom = AlgHom.id K M := by
  apply AdjoinRoot.algHom_ext
  change toCompositumHom (fromCompositumHom s) = s
  rw [fromCompositumHom_s]
  simpa only [recoveredS, map_div₀, _root_.map_add,
    _root_.map_sub, _root_.map_mul, _root_.map_pow,
    _root_.map_ofNat, toCompositumHom_genericRoot] using
      recover_s_in_compositum

private theorem from_to :
    fromCompositumHom.comp toCompositumHom =
      AlgHom.id K descentCurve.toAffine.A := by
  apply AdjoinRoot.algHom_ext
  change fromCompositumHom (toCompositumHom genericRoot) = genericRoot
  rw [toCompositumHom_genericRoot]
  simpa only [descentRootInM, relativeTwoDivisionZ, map_div₀,
    _root_.map_add, _root_.map_sub, _root_.map_mul, _root_.map_pow,
    _root_.map_inv₀, _root_.map_ofNat, fromCompositumHom_s,
    AlgHom.commutes] using recover_genericRoot

/-- The generic `x - T` algebra is the explicit degree-nine compositum,
as an algebra over the real cubic coefficient field. -/
def descentAlgebraEquiv : descentCurve.toAffine.A ≃ₐ[K] M :=
  AlgEquiv.ofAlgHom toCompositumHom fromCompositumHom to_from from_to

@[simp]
theorem descentAlgebraEquiv_genericRoot :
    descentAlgebraEquiv genericRoot = descentRootInM := by
  exact toCompositumHom_genericRoot



end

end MazurTorsion.XOneEighteenDescentAlgebraEquiv

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


/- Source module: MazurTorsion.NumberTheory.XOneEighteenMinimalTwoDescentModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# A dyadic-support two-descent model for the `X₁(18)` quotient

The rational-coefficient model used for explicit two-division arithmetic is
obtained from the original real-cubic quotient by a change with scale `3`.
It is consequently nonminimal at the primes above `3`.  For the global
Selmer containment we instead complete the square directly on the original
quotient, whose discriminant is `-2`.

The abscissas on the two completed-square models are related by

`z = 9 w + 3τ² + 3τ - 8`.

Thus the new cubic algebra is the same explicit degree-nine compositum, but
its bad-prime support is genuinely dyadic.
-/

open Polynomial WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenMinimalTwoDescentModel

noncomputable section

open MazurTorsion.XOneEighteenRealCubicQuotient
open MazurTorsion.XOneEighteenQuotientTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenDescentAlgebraEquiv



private theorem tau_pow_four : tau ^ 4 = 3 * tau ^ 2 + tau := by
  calc
    tau ^ 4 = tau * tau ^ 3 := by ring
    _ = 3 * tau ^ 2 + tau := by rw [tau_cubic]; ring



/-- Exact coefficients of the minimal completed-square model. -/
theorem minimalDescentCurve_eq :
    minimalDescentCurve =
      (⟨0, tau ^ 2 + tau - (11 : K) / 4, 0,
          (-tau ^ 2 + tau + 7) / 2,
          (2 * tau ^ 2 + tau - 5) / 4⟩ : WeierstrassCurve K) := by
  ext
  all_goals
    norm_num [minimalDescentCurve, quotientCurve,
      WeierstrassCurve.toCharNeTwoNF,
      WeierstrassCurve.variableChange_a₁,
      WeierstrassCurve.variableChange_a₂,
      WeierstrassCurve.variableChange_a₃,
      WeierstrassCurve.variableChange_a₄,
      WeierstrassCurve.variableChange_a₆]
  all_goals ring_nf
  all_goals simp only [tau_pow_four, tau_cubic]
  all_goals ring

instance minimalDescentCurve_isElliptic : minimalDescentCurve.IsElliptic := by
  dsimp only [minimalDescentCurve]
  infer_instance

instance minimalDescentCurve_isCharNeTwoNF :
    minimalDescentCurve.IsCharNeTwoNF := by
  dsimp only [minimalDescentCurve]
  infer_instance



/-- The monic cubic for the minimal completed-square model. -/
theorem minimalDescentCurve_f :
    minimalDescentCurve.toAffine.f =
      X ^ 3 + C (tau ^ 2 + tau - (11 : K) / 4) * X ^ 2 +
        C ((-tau ^ 2 + tau + 7) / 2) * X +
          C ((2 * tau ^ 2 + tau - 5) / 4) := by
  rw [minimalDescentCurve_eq]







/-- The affine root change is reversible. -/
theorem descentRootInM_eq_minimal :
    descentRootInM =
      9 * minimalDescentRootInM +
        algebraMap K M rationalAbscissaTranslation := by
  simp only [minimalDescentRootInM]
  field_simp
  ring

/-- The displayed element is a root of the minimal completed-square cubic. -/
theorem minimalDescentRootInM_isRoot :
    Polynomial.IsRoot
      (minimalDescentCurve.toAffine.f.map (algebraMap K M))
        minimalDescentRootInM := by
  have hz :
      4 * descentRootInM ^ 3 - 3 * descentRootInM ^ 2 +
          102 * descentRootInM + 5 = 0 := by
    have h := congrArg descentAlgebraEquiv genericRoot_cubic
    simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat,
      descentAlgebraEquiv_genericRoot, map_zero] using h
  have ht4 : t ^ 4 = 3 * t ^ 2 + t := by
    calc
      t ^ 4 = t * t ^ 3 := by ring
      _ = 3 * t ^ 2 + t := by rw [t_cubic]; ring
  have ht5 : t ^ 5 = t ^ 2 + 9 * t + 3 := by
    calc
      t ^ 5 = t * t ^ 4 := by ring
      _ = 3 * t ^ 3 + t ^ 2 := by rw [ht4]; ring
      _ = t ^ 2 + 9 * t + 3 := by rw [t_cubic]; ring
  have ht6 : t ^ 6 = 9 * t ^ 2 + 6 * t + 1 := by
    calc
      t ^ 6 = t * t ^ 5 := by ring
      _ = t ^ 3 + 9 * t ^ 2 + 3 * t := by rw [ht5]; ring
      _ = 9 * t ^ 2 + 6 * t + 1 := by rw [t_cubic]; ring
  rw [Polynomial.IsRoot, minimalDescentCurve_f,
    Polynomial.eval_map_algebraMap]
  simp only [map_add, map_mul, map_pow, aeval_X, aeval_C]
  simp only [minimalDescentRootInM, rationalAbscissaTranslation,
    map_sub, map_add, map_mul, map_pow, map_ofNat, map_neg,
    map_div₀,
    show algebraMap K M tau = t by rfl]
  field_simp
  ring_nf
  rw [ht6, ht5, ht4, t_cubic]
  ring_nf
  ring_nf at hz
  linear_combination 2 * hz

private theorem minimalDescentRootInM_adjoin_eq_top :
    IntermediateField.adjoin K {minimalDescentRootInM} = ⊤ := by
  let L : IntermediateField K M :=
    IntermediateField.adjoin K {minimalDescentRootInM}
  have hw : minimalDescentRootInM ∈ L :=
    IntermediateField.mem_adjoin_simple_self K minimalDescentRootInM
  have hz : descentRootInM ∈ L := by
    rw [descentRootInM_eq_minimal]
    exact L.add_mem
      (L.mul_mem (L.natCast_mem 9) hw)
      (L.algebraMap_mem rationalAbscissaTranslation)
  have hs : s ∈ L := by
    rw [← recover_s_in_compositum]
    exact L.div_mem
      (L.add_mem
        (L.sub_mem
          (L.mul_mem (L.natCast_mem 4) (L.pow_mem hz 2))
          (L.mul_mem (L.natCast_mem 11) hz))
        (L.natCast_mem 70))
      (L.natCast_mem 27)
  apply top_unique
  intro x _hx
  have hadjoin :
      Algebra.adjoin K ({s} : Set M) ≤ L.toSubalgebra :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hs)
  have hsTop : Algebra.adjoin K ({s} : Set M) = ⊤ := by
    change Algebra.adjoin K
      ({AdjoinRoot.root relativePolynomial} : Set M) = ⊤
    exact AdjoinRoot.adjoinRoot_eq_top
  rw [hsTop] at hadjoin
  exact hadjoin (show x ∈ (⊤ : Subalgebra K M) from trivial)

/-- The minimal completed-square cubic is irreducible over the real cubic
coefficient field. -/
theorem minimalDescentPolynomial_irreducible :
    Irreducible minimalDescentCurve.toAffine.f := by
  have hroot :
      Polynomial.aeval minimalDescentRootInM
        minimalDescentCurve.toAffine.f = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    exact minimalDescentRootInM_isRoot
  have hdegree : (minpoly K minimalDescentRootInM).natDegree = 3 := by
    have h :=
      (Field.primitive_element_iff_minpoly_natDegree_eq
        K minimalDescentRootInM).mp minimalDescentRootInM_adjoin_eq_top
    simpa only [finrank_M_over_K] using h
  have hint : IsIntegral K minimalDescentRootInM :=
    IsIntegral.of_finite K minimalDescentRootInM
  have hdvd : minpoly K minimalDescentRootInM ∣
      minimalDescentCurve.toAffine.f :=
    minpoly.dvd K minimalDescentRootInM hroot
  have heq : minimalDescentCurve.toAffine.f =
      minpoly K minimalDescentRootInM :=
    Polynomial.eq_of_monic_of_dvd_of_natDegree_le
      (minpoly.monic hint) minimalDescentCurve.toAffine.monic_f hdvd (by
        rw [hdegree, minimalDescentCurve.toAffine.natDegree_f])
  rw [heq]
  exact minpoly.irreducible hint

private instance minimalDescentPolynomial_irreducibleFact :
    Fact (Irreducible minimalDescentCurve.toAffine.f) :=
  ⟨minimalDescentPolynomial_irreducible⟩

/-- The distinguished root in the generic minimal descent algebra. -/
def minimalGenericRoot : minimalDescentCurve.toAffine.A :=
  AdjoinRoot.root minimalDescentCurve.toAffine.f

/-- The canonical map from the generic minimal descent algebra to the
explicit degree-nine compositum. -/
def minimalToCompositumHom : minimalDescentCurve.toAffine.A →ₐ[K] M :=
  AdjoinRoot.liftAlgHom minimalDescentCurve.toAffine.f (Algebra.ofId K M)
    minimalDescentRootInM (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      rw [← Polynomial.eval_map_algebraMap]
      exact minimalDescentRootInM_isRoot)

@[simp]
theorem minimalToCompositumHom_genericRoot :
    minimalToCompositumHom minimalGenericRoot = minimalDescentRootInM := by
  exact AdjoinRoot.liftAlgHom_root minimalDescentCurve.toAffine.f _ _ _

private theorem minimalToCompositumHom_bijective :
    Function.Bijective minimalToCompositumHom := by
  letI : Module.Finite K minimalDescentCurve.toAffine.A :=
    (AdjoinRoot.powerBasis minimalDescentCurve.toAffine.f_ne_zero).finite
  have hinjective : Function.Injective minimalToCompositumHom :=
    minimalToCompositumHom.toRingHom.injective
  have hfinrank :
      Module.finrank K minimalDescentCurve.toAffine.A =
        Module.finrank K M := by
    rw [minimalDescentCurve.toAffine.finrank_A, finrank_M_over_K]
  have hsurjective : Function.Surjective minimalToCompositumHom :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := minimalToCompositumHom.toLinearMap) hfinrank).mp hinjective
  exact ⟨hinjective, hsurjective⟩

/-- The minimal dyadic-support descent algebra is the explicit degree-nine
compositum, as a `K`-algebra. -/
def minimalDescentAlgebraEquiv :
    minimalDescentCurve.toAffine.A ≃ₐ[K] M :=
  AlgEquiv.ofBijective minimalToCompositumHom
    minimalToCompositumHom_bijective

@[simp]
theorem minimalDescentAlgebraEquiv_genericRoot :
    minimalDescentAlgebraEquiv minimalGenericRoot =
      minimalDescentRootInM := by
  exact minimalToCompositumHom_genericRoot

/-- The induced equivalence on square classes. -/
def minimalDescentSquareclassEquiv :
    minimalDescentCurve.toAffine.M ≃* Units.modPow M 2 :=
  Units.modPow.congr minimalDescentAlgebraEquiv.toMulEquiv 2



end

end MazurTorsion.XOneEighteenMinimalTwoDescentModel

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



/-- Genuine reduction from the integer ring of the coefficient-field
completion to the explicit cubic ring modulo `2⁷`. -/
noncomputable def completionReduction :
    coefficientPrimeTwo.adicCompletionIntegers Q.K →+* CubicResidue128 :=
  cubicResidue128EquivGlobal.symm.toRingHom.comp
    ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm.toRingHom.comp
      (Ideal.Quotient.mk
        (IsLocalRing.maximalIdeal
          (coefficientPrimeTwo.adicCompletionIntegers Q.K) ^ 7)))

theorem cubicResidue128EquivGlobal_completionReduction_algebraMap
    (r : 𝓞 Q.K) :
    cubicResidue128EquivGlobal
        (completionReduction
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) r)) =
      Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7) r := by
  calc
    cubicResidue128EquivGlobal
        (completionReduction
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) r)) =
      (completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
        (Ideal.Quotient.mk
          (IsLocalRing.maximalIdeal
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) ^ 7)
          (algebraMap (𝓞 Q.K)
            (coefficientPrimeTwo.adicCompletionIntegers Q.K) r)) := by
        change cubicResidue128EquivGlobal
          (cubicResidue128EquivGlobal.symm _) = _
        exact RingEquiv.apply_symm_apply _ _
    _ = Ideal.Quotient.mk (coefficientPrimeTwo.asIdeal ^ 7) r := by
      rw [← completionQuotientEquiv_mk]
      exact RingEquiv.symm_apply_apply _ _



/-! ## The selected simple root of the local two-division cubic -/









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



private theorem three_not_mem_completionMaximalIdeal :
    (3 : CoefficientCompletionIntegers) ∉
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  intro hthree
  have h := (coefficientPrimeTwo.algebraMap_mem_maximalIdeal_pow_iff
    (K := Q.K) (r := (3 : 𝓞 Q.K)) (n := 1)).1 (by
      simpa only [pow_one, map_ofNat] using hthree)
  exact three_not_mem_coefficientPrimeTwo (by
    simpa only [pow_one] using h)









private theorem seventyFour_mem_completionMaximalIdeal :
    (74 : CoefficientCompletionIntegers) ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
  have hglobal : (74 : 𝓞 Q.K) ∈ coefficientPrimeTwo.asIdeal := by
    rw [coefficientPrimeTwo_span, Ideal.mem_span_singleton]
    exact ⟨37, by norm_num⟩
  have h := (coefficientPrimeTwo.algebraMap_mem_maximalIdeal_pow_iff
    (K := Q.K) (r := (74 : 𝓞 Q.K)) (n := 1)).2 (by
      simpa only [pow_one] using hglobal)
  simpa only [pow_one, map_ofNat] using h

private def localTwoDivisionRootCofactor : CoefficientCompletionIntegers :=
  localTwoDivisionRoot ^ 2 + 74 * localTwoDivisionRoot + 74 ^ 2 - 3

private theorem localTwoDivisionRootCofactor_isUnit :
    IsUnit localTwoDivisionRootCofactor := by
  let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers
  have hrest : localTwoDivisionRoot ^ 2 +
      74 * localTwoDivisionRoot + 74 ^ 2 ∈ I := by
    apply I.add_mem
    · apply I.add_mem
      · simpa only [pow_two] using
          I.mul_mem_left localTwoDivisionRoot
            localTwoDivisionRoot_mem_maximalIdeal
      · exact I.mul_mem_left 74 localTwoDivisionRoot_mem_maximalIdeal
    · simpa only [pow_two] using
        I.mul_mem_left 74 seventyFour_mem_completionMaximalIdeal
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hcofactor
  have hnegthree : (-3 : CoefficientCompletionIntegers) ∈ I := by
    have hsub := I.sub_mem hcofactor hrest
    change localTwoDivisionRootCofactor -
      (localTwoDivisionRoot ^ 2 + 74 * localTwoDivisionRoot + 74 ^ 2) ∈ I at hsub
    have heq : localTwoDivisionRootCofactor -
        (localTwoDivisionRoot ^ 2 + 74 * localTwoDivisionRoot + 74 ^ 2) =
          (-3 : CoefficientCompletionIntegers) := by
      simp only [localTwoDivisionRootCofactor]
      ring
    rw [heq] at hsub
    exact hsub
  have hthree : (3 : CoefficientCompletionIntegers) ∈ I := by
    simpa only [neg_neg] using I.neg_mem hnegthree
  exact three_not_mem_completionMaximalIdeal hthree

private theorem oneTwentyEight_mem_completionMaximalIdeal_pow_seven :
    (128 : CoefficientCompletionIntegers) ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 := by
  have hglobal : (128 : 𝓞 Q.K) ∈ coefficientPrimeTwo.asIdeal ^ 7 := by
    rw [coefficientPrimeTwo_pow_seven]
    exact Ideal.subset_span (Set.mem_singleton 128)
  have h := (coefficientPrimeTwo.algebraMap_mem_maximalIdeal_pow_iff
    (K := Q.K) (r := (128 : 𝓞 Q.K)) (n := 7)).2 hglobal
  simpa only [map_ofNat] using h

/-- The chosen Hensel root has the certified residue `74` modulo `2⁷`.
The proof uses the exact factorization of the difference of the two cubic
values and cancellation of a unit, rather than uniqueness as an oracle. -/
theorem localTwoDivisionRoot_sub_seventyFour_mem_pow_seven :
    localTwoDivisionRoot - 74 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 := by
  let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7
  have hroot : localTwoDivisionRoot ^ 3 -
      3 * localTwoDivisionRoot - 10 = 0 := by
    simpa only [Polynomial.IsRoot, localTwoDivisionPolynomial,
      eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat] using
      localTwoDivisionRoot_isRoot
  have hfactor :
      (localTwoDivisionRoot - 74) * localTwoDivisionRootCofactor =
        -(128 * 3164) := by
    simp only [localTwoDivisionRootCofactor]
    linear_combination hroot
  have hrhs : (-(128 * 3164) : CoefficientCompletionIntegers) ∈ I := by
    exact I.neg_mem
      (I.mul_mem_right 3164
        oneTwentyEight_mem_completionMaximalIdeal_pow_seven)
  have hproduct :
      (localTwoDivisionRoot - 74) * localTwoDivisionRootCofactor ∈ I := by
    rw [hfactor]
    exact hrhs
  exact (I.mul_unit_mem_iff_mem
    localTwoDivisionRootCofactor_isUnit).mp hproduct

private theorem completionReduction_seventyFour :
    completionReduction (74 : CoefficientCompletionIntegers) =
      (74 : CubicResidue128) := by
  apply cubicResidue128EquivGlobal.injective
  have hseventyFour : (74 : CoefficientCompletionIntegers) =
      algebraMap (𝓞 Q.K) CoefficientCompletionIntegers (74 : 𝓞 Q.K) := by
    simp only [map_ofNat]
  rw [hseventyFour,
    cubicResidue128EquivGlobal_completionReduction_algebraMap]
  simp only [map_ofNat]

/-- Under the genuine completion reduction, the Hensel-lifted
two-division root specializes to the checked scalar root `74`. -/
theorem completionReduction_localTwoDivisionRoot :
    completionReduction localTwoDivisionRoot = 74 := by
  rw [← completionReduction_seventyFour]
  change
    cubicResidue128EquivGlobal.symm
        ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7)
            localTwoDivisionRoot)) =
      cubicResidue128EquivGlobal.symm
        ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7) 74))
  apply congrArg (fun q ↦ cubicResidue128EquivGlobal.symm
    ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm q))
  exact Ideal.Quotient.eq.mpr
    localTwoDivisionRoot_sub_seventyFour_mem_pow_seven

/-! ## The unramified dyadic uniformizer and square lifting -/

/-- The rational integer `2` is a uniformizer in the selected completion.
This is where unramifiedness of the coefficient-field prime is used. -/
theorem coefficientCompletion_maximalIdeal_eq_span_two :
    IsLocalRing.maximalIdeal CoefficientCompletionIntegers =
      Ideal.span {(2 : CoefficientCompletionIntegers)} := by
  have h := coefficientPrimeTwo.span_singleton_eq_maximalIdeal_pow
    (K := Q.K) (x := (2 : CoefficientCompletionIntegers)) (e := 1) (by
      simp only [map_ofNat]
      calc
        Valued.v (2 : coefficientPrimeTwo.adicCompletion Q.K) =
            Valued.v (algebraMap Q.K
              (coefficientPrimeTwo.adicCompletion Q.K) (2 : Q.K)) := by
          exact congrArg Valued.v (by simp only [map_ofNat])
        _ = coefficientPrimeTwo.valuation Q.K (2 : Q.K) := by
          rw [IsDedekindDomain.HeightOneSpectrum.algebraMap_adicCompletion
            (𝓞 Q.K) Q.K coefficientPrimeTwo]
          exact coefficientPrimeTwo.valuedAdicCompletion_eq_valuation'
            (2 : Q.K)
        _ = coefficientPrimeTwo.intValuation (2 : 𝓞 Q.K) := by
          simpa only [map_ofNat] using
            coefficientPrimeTwo.valuation_of_algebraMap
              (K := Q.K) (2 : 𝓞 Q.K)
        _ = exp (-1) := by
          rw [coefficientPrimeTwo.intValuation_eq_exp_neg_multiplicity
              (by norm_num),
            coefficientPrimeTwo_span]
          simp)
  simpa only [pow_one] using h.symm

private theorem coefficientCompletion_maximalIdeal_pow_eq_span_two_pow
    (n : ℕ) :
    IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ n =
      Ideal.span {(2 ^ n : CoefficientCompletionIntegers)} := by
  rw [coefficientCompletion_maximalIdeal_eq_span_two,
    Ideal.span_singleton_pow]

private theorem completionReduction_surjective :
    Function.Surjective completionReduction :=
  cubicResidue128EquivGlobal.symm.surjective.comp
    ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm.surjective.comp
      Ideal.Quotient.mk_surjective)

private theorem completionReduction_eq_iff
    (x y : CoefficientCompletionIntegers) :
    completionReduction x = completionReduction y ↔
      x - y ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 := by
  change
    cubicResidue128EquivGlobal.symm
        ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7) x)) =
      cubicResidue128EquivGlobal.symm
        ((completionQuotientEquiv (K := Q.K) coefficientPrimeTwo 7).symm
          (Ideal.Quotient.mk
            (IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7) y)) ↔ _
  rw [cubicResidue128EquivGlobal.symm.injective.eq_iff,
    (completionQuotientEquiv
      (K := Q.K) coefficientPrimeTwo 7).symm.injective.eq_iff,
    Ideal.Quotient.eq]

private theorem exists_eq_eight_mul_of_mem_maximalIdeal_pow_seven
    {x : CoefficientCompletionIntegers}
    (hx : x ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7) :
    ∃ a : CoefficientCompletionIntegers, x = 8 * a := by
  have hxthree : x ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 3 :=
    (Ideal.pow_le_pow_right (by norm_num : 3 ≤ 7)) hx
  rw [coefficientCompletion_maximalIdeal_pow_eq_span_two_pow,
    show (2 : CoefficientCompletionIntegers) ^ 3 = 8 by norm_num,
    Ideal.mem_span_singleton] at hxthree
  obtain ⟨a, ha⟩ := hxthree
  exact ⟨a, by simpa only [mul_comm] using ha⟩

/-- A unit square modulo `2³` lifts to a square in the Henselian dyadic
integer ring.  Replacing `z` by `z + 2t` turns the nonsimple square-root
equation into a monic polynomial with unit derivative. -/
private theorem isSquare_of_eq_sq_add_eight_mul
    {u z a : CoefficientCompletionIntegers} (hz : IsUnit z)
    (hu : u = z ^ 2 + 8 * a) : IsSquare u := by
  let f : Polynomial CoefficientCompletionIntegers :=
    X ^ 2 + C z * X - C (2 * a)
  have hfmonic : f.Monic := by
    dsimp only [f]
    monicity <;> norm_num
  have hfzero : f.eval 0 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
    have htwo : (2 : CoefficientCompletionIntegers) ∈
        IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
      rw [coefficientCompletion_maximalIdeal_eq_span_two,
        Ideal.mem_span_singleton]
    have hmem := (IsLocalRing.maximalIdeal
      CoefficientCompletionIntegers).mul_mem_right a htwo
    have heval : f.eval 0 = -(2 * a) := by
      norm_num [f]
    rw [heval]
    exact (IsLocalRing.maximalIdeal
      CoefficientCompletionIntegers).neg_mem hmem
  have hfderiv : IsUnit (f.derivative.eval 0) := by
    have heval : f.derivative.eval 0 = z := by
      norm_num [f]
    rw [heval]
    exact hz
  obtain ⟨t, ht, -⟩ := HenselianLocalRing.is_henselian
    f hfmonic 0 hfzero hfderiv
  refine ⟨z + 2 * t, ?_⟩
  have hroot : t ^ 2 + z * t - 2 * a = 0 := by
    simpa only [Polynomial.IsRoot, f, eval_sub, eval_add, eval_pow,
      eval_X, eval_mul, eval_C] using ht
  rw [hu]
  linear_combination -4 * hroot

/-! ## The normalized projected curve over the integer ring -/

/-- The integral quadratic coefficient after translating to the selected
two-division root and scaling the abscissa by `4`. -/
def localNormalizedA : CoefficientCompletionIntegers :=
  9 * (localTwoDivisionRoot ^ 2 - 2 * localTwoDivisionRoot - 2)

/-- The integral constant coefficient in the same normalized model. -/
def localNormalizedB : CoefficientCompletionIntegers :=
  81 * (localTwoDivisionRoot ^ 2 + 2 * localTwoDivisionRoot - 7)

private theorem scalar_one_twenty_eight_eq_zero :
    (128 : CubicResidue128) = 0 := by
  rw [← map_ofNat (algebraMap (ZMod 128) CubicResidue128) 128]
  have h : (128 : ZMod 128) = 0 := by decide
  rw [h, map_zero]

@[simp] theorem completionReduction_localNormalizedA :
    completionReduction localNormalizedA = 62 := by
  simp only [localNormalizedA, map_mul, map_sub, map_pow,
    map_ofNat, completionReduction_localTwoDivisionRoot]
  linear_combination 374 * scalar_one_twenty_eight_eq_zero

@[simp] theorem completionReduction_localNormalizedB :
    completionReduction localNormalizedB = 65 := by
  simp only [localNormalizedB, map_mul, map_sub, map_add, map_pow,
    map_ofNat, completionReduction_localTwoDivisionRoot]
  linear_combination 3554 * scalar_one_twenty_eight_eq_zero

private theorem normalizedQuadratic_reduction_eq_square
    (x : CoefficientCompletionIntegers) :
    completionReduction
        (x ^ 2 + localNormalizedA * x + localNormalizedB) =
      completionReduction (x + 31) ^ 2 := by
  simp only [map_add, map_mul, map_pow,
    completionReduction_localNormalizedA,
    completionReduction_localNormalizedB, map_ofNat]
  linear_combination -7 * scalar_one_twenty_eight_eq_zero

private theorem isUnit_of_add_mem_maximalIdeal
    {u m : CoefficientCompletionIntegers} (hu : IsUnit u)
    (hm : m ∈ IsLocalRing.maximalIdeal CoefficientCompletionIntegers) :
    IsUnit (u + m) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro hum
  have huMem := (IsLocalRing.maximalIdeal
    CoefficientCompletionIntegers).sub_mem hum hm
  have huNotMem := IsLocalRing.notMem_maximalIdeal.mpr hu
  exact huNotMem (by simpa only [add_sub_cancel_right] using huMem)

private theorem isSquare_of_isUnit_of_reduction_isSquare
    {x : CoefficientCompletionIntegers} (hx : IsUnit x)
    (hred : IsSquare (completionReduction x)) : IsSquare x := by
  obtain ⟨zBar, hzBar⟩ := hred
  obtain ⟨z, hz⟩ := completionReduction_surjective zBar
  have hredEq : completionReduction x = completionReduction (z ^ 2) := by
    rw [map_pow, hz]
    simpa only [pow_two] using hzBar
  have hdiff : x - z ^ 2 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 :=
    (completionReduction_eq_iff x (z ^ 2)).1 hredEq
  obtain ⟨a, ha⟩ :=
    exists_eq_eight_mul_of_mem_maximalIdeal_pow_seven hdiff
  have hzUnit : IsUnit z := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hzMem
    let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers
    have hzSqMem : z ^ 2 ∈ I := by
      simpa only [pow_two] using I.mul_mem_left z hzMem
    have hdiffMem : x - z ^ 2 ∈ I := by
      change x - z ^ 2 ∈
        IsLocalRing.maximalIdeal CoefficientCompletionIntegers
      simpa only [pow_one] using
        (Ideal.pow_le_pow_right (by norm_num : 1 ≤ 7)) hdiff
    have hxMem : x ∈ I := by
      have hsum := I.add_mem hzSqMem hdiffMem
      have heq : z ^ 2 + (x - z ^ 2) = x := by ring
      rwa [heq] at hsum
    exact (IsLocalRing.notMem_maximalIdeal.mpr hx) hxMem
  exact isSquare_of_eq_sq_add_eight_mul hzUnit (a := a) (by
    linear_combination ha)

private theorem thirtyOne_isUnit :
    IsUnit (31 : CoefficientCompletionIntegers) := by
  apply IsLocalRing.notMem_maximalIdeal.mp
  intro h31
  let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers
  have htwo : (2 : CoefficientCompletionIntegers) ∈ I := by
    change (2 : CoefficientCompletionIntegers) ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers
    rw [coefficientCompletion_maximalIdeal_eq_span_two,
      Ideal.mem_span_singleton]
  have hthirty : (30 : CoefficientCompletionIntegers) ∈ I := by
    have h := I.mul_mem_right 15 htwo
    norm_num at h
    exact h
  have hone : (1 : CoefficientCompletionIntegers) ∈ I := by
    have hsub := I.sub_mem h31 hthirty
    norm_num at hsub
    exact hsub
  exact (IsLocalRing.maximalIdeal.isMaximal
    CoefficientCompletionIntegers).ne_top
      ((Ideal.eq_top_iff_one _).mpr hone)

private theorem normalizedQuadratic_isSquare_of_nonunit
    {x : CoefficientCompletionIntegers} (hx : ¬ IsUnit x) :
    IsSquare (x ^ 2 + localNormalizedA * x + localNormalizedB) := by
  let q := x ^ 2 + localNormalizedA * x + localNormalizedB
  let z := x + 31
  have hxMem : x ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
    by_contra hxNotMem
    exact hx (IsLocalRing.notMem_maximalIdeal.mp hxNotMem)
  have hzUnit : IsUnit z := by
    simpa only [z, add_comm] using
      isUnit_of_add_mem_maximalIdeal thirtyOne_isUnit hxMem
  have hred : completionReduction q = completionReduction (z ^ 2) := by
    rw [map_pow]
    simpa only [q, z] using normalizedQuadratic_reduction_eq_square x
  have hdiff : q - z ^ 2 ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 :=
    (completionReduction_eq_iff q (z ^ 2)).1 hred
  obtain ⟨a, ha⟩ :=
    exists_eq_eight_mul_of_mem_maximalIdeal_pow_seven hdiff
  exact isSquare_of_eq_sq_add_eight_mul hzUnit (a := a) (by
    dsimp only [q, z]
    dsimp only [q, z] at ha
    linear_combination ha)

private theorem normalizedQuadratic_isUnit_of_nonunit
    {x : CoefficientCompletionIntegers} (hx : ¬ IsUnit x) :
    IsUnit (x ^ 2 + localNormalizedA * x + localNormalizedB) := by
  let I := IsLocalRing.maximalIdeal CoefficientCompletionIntegers
  have hxMem : x ∈ I := by
    by_contra hxNotMem
    exact hx (IsLocalRing.notMem_maximalIdeal.mp hxNotMem)
  have hrest : x ^ 2 + localNormalizedA * x ∈ I := by
    apply I.add_mem
    · simpa only [pow_two] using I.mul_mem_left x hxMem
    · exact I.mul_mem_left localNormalizedA hxMem
  have hBUnit : IsUnit localNormalizedB := by
    have hsixtyFive : IsUnit (65 : CoefficientCompletionIntegers) := by
      have hsixtyFour : (64 : CoefficientCompletionIntegers) ∈ I := by
        have htwo : (2 : CoefficientCompletionIntegers) ∈ I := by
          change (2 : CoefficientCompletionIntegers) ∈
            IsLocalRing.maximalIdeal CoefficientCompletionIntegers
          rw [coefficientCompletion_maximalIdeal_eq_span_two,
            Ideal.mem_span_singleton]
        have h := I.mul_mem_right 32 htwo
        norm_num at h
        exact h
      have h := isUnit_of_add_mem_maximalIdeal isUnit_one hsixtyFour
      norm_num at h
      exact h
    have hred : completionReduction localNormalizedB =
        completionReduction (65 : CoefficientCompletionIntegers) := by
      rw [completionReduction_localNormalizedB, map_ofNat]
    have hdiffPow : localNormalizedB - 65 ∈
        IsLocalRing.maximalIdeal CoefficientCompletionIntegers ^ 7 :=
      (completionReduction_eq_iff localNormalizedB 65).1 hred
    have hdiff : localNormalizedB - 65 ∈ I := by
      change localNormalizedB - 65 ∈
        IsLocalRing.maximalIdeal CoefficientCompletionIntegers
      simpa only [pow_one] using
        (Ideal.pow_le_pow_right (by norm_num : 1 ≤ 7)) hdiffPow
    have hsum := isUnit_of_add_mem_maximalIdeal hsixtyFive hdiff
    have heq : (65 : CoefficientCompletionIntegers) +
        (localNormalizedB - 65) = localNormalizedB := by ring
    rwa [heq] at hsum
  have hsum := isUnit_of_add_mem_maximalIdeal hBUnit hrest
  have heq : localNormalizedB +
      (x ^ 2 + localNormalizedA * x) =
        x ^ 2 + localNormalizedA * x + localNormalizedB := by ring
  rwa [heq] at hsum

/-- The adjusted value at the selected two-torsion abscissa is a square.
Its residue is `65 = 33²` modulo `2⁷`, and the unit square lifts by the
Henselian lemma above. -/
theorem localNormalizedB_isSquare : IsSquare localNormalizedB := by
  have hBUnit : IsUnit localNormalizedB := by
    have h := normalizedQuadratic_isUnit_of_nonunit
      (x := (0 : CoefficientCompletionIntegers)) not_isUnit_zero
    simpa only [zero_pow (by norm_num : 2 ≠ 0), zero_mul, mul_zero,
      zero_add] using h
  apply isSquare_of_isUnit_of_reduction_isSquare hBUnit
  refine ⟨(33 : CubicResidue128), ?_⟩
  rw [completionReduction_localNormalizedB]
  linear_combination -8 * scalar_one_twenty_eight_eq_zero

/-- Every integral point of the genuinely normalized projected curve has
square first coordinate in the completion's integer ring. -/
theorem normalized_integral_curve_isSquare
    (x y : CoefficientCompletionIntegers)
    (hcurve : y ^ 2 =
      x * (x ^ 2 + localNormalizedA * x + localNormalizedB)) :
    IsSquare x := by
  by_cases hx : IsUnit x
  · apply isSquare_of_isUnit_of_reduction_isSquare hx
    apply XOneEighteenDyadicLocalImage.integral_cubic_mod128
      (completionReduction x) (completionReduction y)
    have hred := congrArg completionReduction hcurve
    simpa only [map_pow, map_mul, map_add,
      completionReduction_localNormalizedA,
      completionReduction_localNormalizedB] using hred
  · have hqSquare := normalizedQuadratic_isSquare_of_nonunit hx
    have hqUnit := normalizedQuadratic_isUnit_of_nonunit hx
    obtain ⟨w, hw⟩ := hqSquare
    have hwUnit : IsUnit w := by
      have hwwUnit : IsUnit (w * w) := by
        rw [← hw]
        exact hqUnit
      exact (IsUnit.mul_iff.mp hwwUnit).1
    let wInv : CoefficientCompletionIntegers := ↑(hwUnit.unit⁻¹)
    have hwwInv : w * wInv = 1 := by
      dsimp only [wInv]
      calc
        w * (↑(hwUnit.unit⁻¹) : CoefficientCompletionIntegers) =
            (↑hwUnit.unit : CoefficientCompletionIntegers) *
              (↑(hwUnit.unit⁻¹) : CoefficientCompletionIntegers) := by
          rw [hwUnit.unit_spec]
        _ = 1 := by simp
    have hy : y ^ 2 = x * w ^ 2 := by
      calc
        y ^ 2 = x *
            (x ^ 2 + localNormalizedA * x + localNormalizedB) := hcurve
        _ = x * (w * w) := by rw [hw]
        _ = x * w ^ 2 := by rw [pow_two]
    refine ⟨y * wInv, ?_⟩
    calc
      x = x * (w * wInv) ^ 2 := by rw [hwwInv]; ring
      _ = (x * w ^ 2) * wInv ^ 2 := by ring
      _ = y ^ 2 * wInv ^ 2 := by rw [hy]
      _ = (y * wInv) * (y * wInv) := by ring

/-! ## Passage to the completion field -/



private theorem coefficientCompletion_two_ne_zero :
    (2 : CoefficientCompletion) ≠ 0 := by
  simpa only [map_ofNat] using
    (_root_.map_ne_zero (algebraMap Q.K CoefficientCompletion)).mpr
      (by norm_num : (2 : Q.K) ≠ 0)

private theorem coefficientCompletion_four_ne_zero :
    (4 : CoefficientCompletion) ≠ 0 := by
  simpa only [map_ofNat] using
    (_root_.map_ne_zero (algebraMap Q.K CoefficientCompletion)).mpr
      (by norm_num : (4 : Q.K) ≠ 0)

private theorem coefficientCompletion_natCast_ne_zero
    {n : ℕ} (hn : n ≠ 0) : (n : CoefficientCompletion) ≠ 0 := by
  simpa only [map_natCast] using
    (_root_.map_ne_zero (algebraMap Q.K CoefficientCompletion)).mpr
      (Nat.cast_ne_zero.mpr hn : (n : Q.K) ≠ 0)

private theorem field_isSquare_of_integer_isSquare
    (x : CoefficientCompletionIntegers) (hx : IsSquare x) :
    IsSquare (x : CoefficientCompletion) := by
  obtain ⟨z, hz⟩ := hx
  refine ⟨(z : CoefficientCompletion), ?_⟩
  exact congrArg Subtype.val hz

private theorem integer_ordinate_of_integer_abscissa
    (x : CoefficientCompletionIntegers) (y : CoefficientCompletion)
    (hcurve : y ^ 2 =
      (x : CoefficientCompletion) *
        ((x : CoefficientCompletion) ^ 2 +
          (localNormalizedA : CoefficientCompletion) * x +
          localNormalizedB)) :
    ∃ yInt : CoefficientCompletionIntegers, (yInt : CoefficientCompletion) = y := by
  let rhs : CoefficientCompletionIntegers :=
    x * (x ^ 2 + localNormalizedA * x + localNormalizedB)
  have hySqLe : Valued.v (y ^ 2) ≤ (1 : ℤᵐ⁰) := by
    rw [hcurve]
    change Valued.v (rhs : CoefficientCompletion) ≤ (1 : ℤᵐ⁰)
    exact rhs.2
  have hyLe : Valued.v y ≤ (1 : ℤᵐ⁰) := by
    apply (sq_le_one_iff₀ bot_le).mp
    rw [← map_pow]
    exact hySqLe
  exact ⟨⟨y, hyLe⟩, rfl⟩

private theorem normalized_curve_isSquare_of_integral_abscissa
    (x y : CoefficientCompletion)
    (hx : Valued.v x ≤ (1 : ℤᵐ⁰))
    (hcurve : y ^ 2 = x *
      (x ^ 2 + (localNormalizedA : CoefficientCompletion) * x +
        localNormalizedB)) :
    IsSquare x := by
  let xInt : CoefficientCompletionIntegers := ⟨x, hx⟩
  obtain ⟨yInt, hyInt⟩ := integer_ordinate_of_integer_abscissa xInt y (by
    simpa only [xInt] using hcurve)
  have hcurveInt : yInt ^ 2 =
      xInt * (xInt ^ 2 + localNormalizedA * xInt + localNormalizedB) := by
    apply Subtype.ext
    change (yInt : CoefficientCompletion) ^ 2 = x *
      (x ^ 2 + (localNormalizedA : CoefficientCompletion) * x +
        localNormalizedB)
    rw [hyInt]
    exact hcurve
  have hxSquare := normalized_integral_curve_isSquare xInt yInt hcurveInt
  simpa only [xInt] using field_isSquare_of_integer_isSquare xInt hxSquare

private theorem exists_localNormalizedA_eq_two_mul :
    ∃ a : CoefficientCompletionIntegers, localNormalizedA = 2 * a := by
  have hs : localTwoDivisionRoot ∈
      Ideal.span {(2 : CoefficientCompletionIntegers)} := by
    rw [← coefficientCompletion_maximalIdeal_eq_span_two]
    exact localTwoDivisionRoot_mem_maximalIdeal
  rw [Ideal.mem_span_singleton] at hs
  obtain ⟨c, hc⟩ := hs
  refine ⟨9 * (2 * c ^ 2 - 2 * c - 1), ?_⟩
  simp only [localNormalizedA]
  rw [hc]
  ring

private theorem isSquare_of_sq_eq_mul_square_of_isUnit
    {u v q : CoefficientCompletionIntegers}
    (hcurve : v ^ 2 = u * q) (hqSquare : IsSquare q)
    (hqUnit : IsUnit q) : IsSquare u := by
  obtain ⟨w, hw⟩ := hqSquare
  have hwUnit : IsUnit w := by
    have hwwUnit : IsUnit (w * w) := by
      rw [← hw]
      exact hqUnit
    exact (IsUnit.mul_iff.mp hwwUnit).1
  let wInv : CoefficientCompletionIntegers := ↑(hwUnit.unit⁻¹)
  have hwwInv : w * wInv = 1 := by
    dsimp only [wInv]
    calc
      w * (↑(hwUnit.unit⁻¹) : CoefficientCompletionIntegers) =
          (↑hwUnit.unit : CoefficientCompletionIntegers) *
            (↑(hwUnit.unit⁻¹) : CoefficientCompletionIntegers) := by
        rw [hwUnit.unit_spec]
      _ = 1 := by simp
  have hv : v ^ 2 = u * w ^ 2 := by
    calc
      v ^ 2 = u * q := hcurve
      _ = u * (w * w) := by rw [hw]
      _ = u * w ^ 2 := by rw [pow_two]
  refine ⟨v * wInv, ?_⟩
  calc
    u = u * (w * wInv) ^ 2 := by rw [hwwInv]; ring
    _ = (u * w ^ 2) * wInv ^ 2 := by ring
    _ = v ^ 2 * wInv ^ 2 := by rw [hv]
    _ = (v * wInv) * (v * wInv) := by ring

private theorem normalized_curve_isSquare_of_pole
    (x y : CoefficientCompletion)
    (hx : 1 < Valued.v x)
    (hcurve : y ^ 2 = x *
      (x ^ 2 + (localNormalizedA : CoefficientCompletion) * x +
        localNormalizedB)) :
    IsSquare x := by
  have hxne : x ≠ 0 := by
    rintro rfl
    simp at hx
  have huValLt : Valued.v x⁻¹ < (1 : ℤᵐ⁰) := by
    rw [map_inv₀, inv_lt_one_iff₀]
    exact Or.inr hx
  let uInt : CoefficientCompletionIntegers := ⟨x⁻¹, huValLt.le⟩
  have huMem : uInt ∈
      IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro huUnit
    have huValEq : Valued.v (uInt : CoefficientCompletion) = 1 :=
      IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one.mp
        huUnit
    exact (ne_of_lt huValLt) huValEq
  let qInt : CoefficientCompletionIntegers :=
    1 + localNormalizedA * uInt + localNormalizedB * uInt ^ 2
  have hqUnit : IsUnit qInt := by
    have hrest : localNormalizedA * uInt +
        localNormalizedB * uInt ^ 2 ∈
          IsLocalRing.maximalIdeal CoefficientCompletionIntegers := by
      apply (IsLocalRing.maximalIdeal
        CoefficientCompletionIntegers).add_mem
      · exact (IsLocalRing.maximalIdeal
          CoefficientCompletionIntegers).mul_mem_left localNormalizedA huMem
      · apply (IsLocalRing.maximalIdeal
          CoefficientCompletionIntegers).mul_mem_left localNormalizedB
        simpa only [pow_two] using
          (IsLocalRing.maximalIdeal
            CoefficientCompletionIntegers).mul_mem_left uInt huMem
    have hunit := isUnit_of_add_mem_maximalIdeal isUnit_one hrest
    have heq : qInt = 1 +
        (localNormalizedA * uInt + localNormalizedB * uInt ^ 2) := by
      dsimp only [qInt]
      ring
    rw [heq]
    exact hunit
  let vField : CoefficientCompletion := y * x⁻¹ ^ 2
  have htrans : vField ^ 2 =
      (uInt : CoefficientCompletion) * (qInt : CoefficientCompletion) := by
    dsimp only [vField, uInt, qInt]
    calc
      (y * x⁻¹ ^ 2) ^ 2 = y ^ 2 * x⁻¹ ^ 4 := by ring
      _ = (x * (x ^ 2 +
          (localNormalizedA : CoefficientCompletion) * x +
            localNormalizedB)) * x⁻¹ ^ 4 := by rw [hcurve]
      _ = x⁻¹ * (1 +
          (localNormalizedA : CoefficientCompletion) * x⁻¹ +
            (localNormalizedB : CoefficientCompletion) * x⁻¹ ^ 2) := by
        field_simp [hxne]
  have hvSqLe : Valued.v (vField ^ 2) ≤ (1 : ℤᵐ⁰) := by
    rw [htrans]
    change Valued.v ((uInt * qInt : CoefficientCompletionIntegers) :
      CoefficientCompletion) ≤ (1 : ℤᵐ⁰)
    exact (uInt * qInt).2
  have hvLe : Valued.v vField ≤ (1 : ℤᵐ⁰) := by
    apply (sq_le_one_iff₀ bot_le).mp
    rw [← map_pow]
    exact hvSqLe
  let vInt : CoefficientCompletionIntegers := ⟨vField, hvLe⟩
  have hcurveInt : vInt ^ 2 = uInt * qInt := by
    apply Subtype.ext
    exact htrans
  have huNe : uInt ≠ 0 := by
    intro hu
    apply inv_ne_zero hxne
    exact congrArg Subtype.val hu
  have hvNe : vInt ≠ 0 := by
    intro hv
    have hzero : (0 : CoefficientCompletionIntegers) = uInt * qInt := by
      simpa only [hv, zero_pow (by norm_num : 2 ≠ 0)] using hcurveInt
    rcases mul_eq_zero.mp hzero.symm with hu | hq
    · exact huNe hu
    · exact hqUnit.ne_zero hq
  have htwoIrr : Irreducible (2 : CoefficientCompletionIntegers) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer 2).2
      coefficientCompletion_maximalIdeal_eq_span_two
  obtain ⟨n, uUnit, huEq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible huNe htwoIrr
  obtain ⟨m, vUnit, hvEq⟩ :=
    IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hvNe htwoIrr
  have huVal : IsDiscreteValuationRing.addVal CoefficientCompletionIntegers uInt = n := by
    rw [huEq]
    exact IsDiscreteValuationRing.addVal_def' uUnit htwoIrr n
  have hvVal : IsDiscreteValuationRing.addVal CoefficientCompletionIntegers vInt = m := by
    rw [hvEq]
    exact IsDiscreteValuationRing.addVal_def' vUnit htwoIrr m
  have hqVal : IsDiscreteValuationRing.addVal CoefficientCompletionIntegers qInt = 0 :=
    IsDiscreteValuationRing.addVal_eq_zero_iff.mpr hqUnit
  have hadd := congrArg
    (IsDiscreteValuationRing.addVal CoefficientCompletionIntegers) hcurveInt
  have hadd' : ((2 : ℕ) : ℕ∞) * (m : ℕ∞) = (n : ℕ∞) := by
    simpa only [IsDiscreteValuationRing.addVal_pow,
      IsDiscreteValuationRing.addVal_mul, hvVal, huVal, hqVal, add_zero,
      nsmul_eq_mul] using hadd
  have hnm : n = 2 * m := by
    exact_mod_cast hadd'.symm
  have hnNe : n ≠ 0 := by
    intro hn
    have huUnit : IsUnit uInt := by
      rw [huEq, hn, pow_zero, mul_one]
      exact uUnit.isUnit
    exact (IsLocalRing.notMem_maximalIdeal.mpr huUnit) huMem
  have hmNe : m ≠ 0 := by
    intro hm
    apply hnNe
    rw [hnm, hm, mul_zero]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hmNe
  have huFour : ∃ c : CoefficientCompletionIntegers, uInt = 4 * c := by
    refine ⟨(uUnit : CoefficientCompletionIntegers) * 2 ^ (2 * k), ?_⟩
    rw [huEq, hnm, hk]
    ring_nf
    rw [Nat.succ_mul, pow_add]
    norm_num
    ring
  obtain ⟨c, hc⟩ := huFour
  obtain ⟨a, ha⟩ := exists_localNormalizedA_eq_two_mul
  have hqForm : qInt = 1 + 8 *
      (a * c + 2 * localNormalizedB * c ^ 2) := by
    dsimp only [qInt]
    rw [ha, hc]
    ring
  have hqSquare : IsSquare qInt :=
    isSquare_of_eq_sq_add_eight_mul (z := 1)
      (a := a * c + 2 * localNormalizedB * c ^ 2) isUnit_one (by
      rw [hqForm]
      ring)
  have huSquare := isSquare_of_sq_eq_mul_square_of_isUnit
    hcurveInt hqSquare hqUnit
  obtain ⟨z, hz⟩ := huSquare
  have hzNe : (z : CoefficientCompletion) ≠ 0 := by
    intro hz0
    have hu0 : uInt = 0 := by
      rw [hz]
      apply Subtype.ext
      change (z : CoefficientCompletion) * z = 0
      rw [hz0, zero_mul]
    exact huNe hu0
  refine ⟨((z : CoefficientCompletion)⁻¹), ?_⟩
  have huField : (x⁻¹ : CoefficientCompletion) =
      (z : CoefficientCompletion) * z := congrArg Subtype.val hz
  calc
    x = (x⁻¹)⁻¹ := (inv_inv x).symm
    _ = ((z : CoefficientCompletion) * z)⁻¹ :=
      congrArg (fun w : CoefficientCompletion => w⁻¹) huField
    _ = (z : CoefficientCompletion)⁻¹ *
        (z : CoefficientCompletion)⁻¹ := by
      rw [mul_inv_rev]

/-- Every point on the normalized projected curve over the genuine
dyadic completion has square abscissa.  The proof treats integral
abscissae through the checked residue certificate and poles by an
even-valuation argument in the completion's discrete valuation ring. -/
theorem normalized_local_curve_isSquare
    (x y : CoefficientCompletion)
    (hcurve : y ^ 2 = x *
      (x ^ 2 + (localNormalizedA : CoefficientCompletion) * x +
        localNormalizedB)) :
    IsSquare x := by
  by_cases hx : Valued.v x ≤ (1 : ℤᵐ⁰)
  · exact normalized_curve_isSquare_of_integral_abscissa x y hx hcurve
  · exact normalized_curve_isSquare_of_pole x y (lt_of_not_ge hx) hcurve

/-! ## Projection of the genuine relative descent algebra -/

private theorem localTwoDivisionRoot_cubic_field :
    (localTwoDivisionRoot : CoefficientCompletion) ^ 3 -
        3 * localTwoDivisionRoot - 10 = 0 := by
  have hroot : localTwoDivisionRoot ^ 3 -
      3 * localTwoDivisionRoot - 10 = 0 := by
    simpa only [Polynomial.IsRoot, localTwoDivisionPolynomial,
      eval_sub, eval_pow, eval_X, eval_mul, eval_ofNat] using
      localTwoDivisionRoot_isRoot
  exact congrArg Subtype.val hroot



@[simp] theorem localRelativeProjection_s :
    localRelativeProjection s =
      (localTwoDivisionRoot : CoefficientCompletion) := by
  exact AdjoinRoot.liftAlgHom_root relativePolynomial _ _ _



/-- The genuine algebra projection sends the explicit compositum root to
the selected local two-torsion abscissa. -/
@[simp] theorem localRelativeProjection_descentRootInM :
    localRelativeProjection descentRootInM =
      localProjectedDescentRoot := by
  simp only [descentRootInM, relativeTwoDivisionZ, map_mul, map_sub,
    map_pow, map_div₀, map_one, map_ofNat,
    localRelativeProjection_s,
    localProjectedDescentRoot]
  ring



private theorem localNormalizedA_eq_projectedRoot :
    (localNormalizedA : CoefficientCompletion) =
      12 * localProjectedDescentRoot - 3 := by
  dsimp only [localNormalizedA, localProjectedDescentRoot]
  change 9 * ((localTwoDivisionRoot : CoefficientCompletion) ^ 2 -
      2 * localTwoDivisionRoot - 2) =
    12 * ((3 * (localTwoDivisionRoot : CoefficientCompletion) ^ 2 -
      6 * localTwoDivisionRoot - 5) / 4) - 3
  field_simp [coefficientCompletion_four_ne_zero]
  ring

private theorem localNormalizedB_eq_projectedDerivative :
    (localNormalizedB : CoefficientCompletion) =
      16 * (3 * localProjectedDescentRoot ^ 2 -
        (3 / 2) * localProjectedDescentRoot + 51 / 2) := by
  let z : CoefficientCompletion :=
    3 * (localTwoDivisionRoot : CoefficientCompletion) ^ 2 -
      6 * localTwoDivisionRoot - 5
  have hBz : (localNormalizedB : CoefficientCompletion) =
      3 * z ^ 2 - 6 * z + 408 := by
    dsimp only [localNormalizedB, z]
    change 81 * ((localTwoDivisionRoot : CoefficientCompletion) ^ 2 +
        2 * localTwoDivisionRoot - 7) =
      3 * (3 * (localTwoDivisionRoot : CoefficientCompletion) ^ 2 -
          6 * localTwoDivisionRoot - 5) ^ 2 -
        6 * (3 * (localTwoDivisionRoot : CoefficientCompletion) ^ 2 -
          6 * localTwoDivisionRoot - 5) + 408
    linear_combination
      -27 * ((localTwoDivisionRoot : CoefficientCompletion) - 4) *
        localTwoDivisionRoot_cubic_field
  rw [hBz]
  change 3 * z ^ 2 - 6 * z + 408 =
    16 * (3 * (z / 4) ^ 2 - (3 / 2) * (z / 4) + 51 / 2)
  field_simp [coefficientCompletion_two_ne_zero,
    coefficientCompletion_four_ne_zero]
  ring





/-- Projection is compatible with the explicit change from the rational
descent algebra to the minimal descent algebra. -/
@[simp] theorem localRelativeProjection_minimalDescentRootInM :
    localRelativeProjection minimalDescentRootInM =
      localProjectedMinimalRoot := by
  simp only [minimalDescentRootInM, map_div₀, map_sub,
    map_ofNat, AlgHom.commutes, localRelativeProjection_descentRootInM,
    localProjectedMinimalRoot]

/-! ## The selected factor of the base-changed minimal descent algebra -/

/-- The minimal descent curve after base change to the selected dyadic
coefficient completion. -/
abbrev LocalMinimalDescentCurve :=
  (minimalDescentCurve⁄CoefficientCompletion).toAffine

private theorem localProjectedMinimalRoot_isRoot :
    LocalMinimalDescentCurve.f.IsRoot localProjectedMinimalRoot := by
  have hglobal : Polynomial.aeval minimalDescentRootInM
      minimalDescentCurve.toAffine.f = 0 := by
    rw [← Polynomial.eval_map_algebraMap]
    exact minimalDescentRootInM_isRoot
  have hlocal := congrArg localRelativeProjection hglobal
  have haeval : Polynomial.aeval localProjectedMinimalRoot
      minimalDescentCurve.toAffine.f = 0 := by
    rw [← localRelativeProjection_minimalDescentRootInM]
    rw [Polynomial.aeval_algHom_apply]
    exact hlocal.trans (map_zero localRelativeProjection)
  rw [Polynomial.IsRoot]
  rw [minimalDescentCurve.toAffine.baseChange_f,
    Polynomial.eval_map_algebraMap]
  exact haeval

/-- Evaluation at the selected minimal root is the actual factor
projection of the base-changed generic descent algebra. -/
noncomputable def localMinimalProjection :
    LocalMinimalDescentCurve.A →ₐ[CoefficientCompletion]
      CoefficientCompletion :=
  AdjoinRoot.liftAlgHom LocalMinimalDescentCurve.f
    (Algebra.ofId CoefficientCompletion CoefficientCompletion)
    localProjectedMinimalRoot (by
      rw [Algebra.toRingHom_ofId, ← aeval_def]
      exact localProjectedMinimalRoot_isRoot)

@[simp] theorem localMinimalProjection_genericRoot :
    localMinimalProjection
        (AdjoinRoot.root LocalMinimalDescentCurve.f) =
      localProjectedMinimalRoot := by
  exact AdjoinRoot.liftAlgHom_root LocalMinimalDescentCurve.f _ _ _

/-- Base change followed by the selected local factor agrees with the
global compositum equivalence followed by `localRelativeProjection`. -/
theorem localMinimalProjection_comp_mapA :
    localMinimalProjection.toRingHom.comp
        (minimalDescentCurve.toAffine.mapA CoefficientCompletion) =
      localRelativeProjection.toRingHom.comp
        minimalDescentAlgebraEquiv.toRingHom := by
  apply AdjoinRoot.ringHom_ext
  · apply DFunLike.ext _ _
    intro x
    change localMinimalProjection
        (minimalDescentCurve.toAffine.mapA CoefficientCompletion
          ((AdjoinRoot.of minimalDescentCurve.toAffine.f) x)) =
      localRelativeProjection
        (minimalDescentAlgebraEquiv
          ((AdjoinRoot.of minimalDescentCurve.toAffine.f) x))
    simp only [WeierstrassCurve.Affine.mapA, AdjoinRoot.map_of]
    rw [← AdjoinRoot.algebraMap_eq,
      localMinimalProjection.commutes,
      ← AdjoinRoot.algebraMap_eq,
      minimalDescentAlgebraEquiv.commutes,
      localRelativeProjection.commutes]
    simp only [Algebra.algebraMap_self, RingHom.id_apply]
  · change localMinimalProjection
        (minimalDescentCurve.toAffine.mapA CoefficientCompletion
          minimalGenericRoot) =
      localRelativeProjection
        (minimalDescentAlgebraEquiv minimalGenericRoot)
    rw [minimalDescentAlgebraEquiv_genericRoot,
      localRelativeProjection_minimalDescentRootInM]
    simp [minimalGenericRoot, WeierstrassCurve.Affine.mapA]

/-! ## The local image of the minimal descent map -/

private theorem localTau_cubic :
    (algebraMap Q.K CoefficientCompletion Q.tau) ^ 3 -
        3 * algebraMap Q.K CoefficientCompletion Q.tau - 1 = 0 := by
  have h := congrArg (algebraMap Q.K CoefficientCompletion) Q.tau_cubic
  simp only [map_pow, map_add, map_mul, map_ofNat, map_one] at h
  linear_combination h

private theorem localMinimalDescentCurve_a₂ :
    LocalMinimalDescentCurve.a₂ =
      algebraMap Q.K CoefficientCompletion
        (Q.tau ^ 2 + Q.tau - (11 : Q.K) / 4) := by
  change algebraMap Q.K CoefficientCompletion minimalDescentCurve.a₂ = _
  rw [minimalDescentCurve_eq]

private theorem localMinimalDescentCurve_a₄ :
    LocalMinimalDescentCurve.a₄ =
      algebraMap Q.K CoefficientCompletion
        ((-Q.tau ^ 2 + Q.tau + 7) / 2) := by
  change algebraMap Q.K CoefficientCompletion minimalDescentCurve.a₄ = _
  rw [minimalDescentCurve_eq]

private theorem localProjectedDescentRoot_eq_minimal :
    localProjectedDescentRoot =
      9 * localProjectedMinimalRoot +
        algebraMap Q.K CoefficientCompletion rationalAbscissaTranslation := by
  dsimp only [localProjectedMinimalRoot]
  have h9 : (9 : CoefficientCompletion) ≠ 0 :=
    coefficientCompletion_natCast_ne_zero (by norm_num)
  rw [div_eq_mul_inv]
  symm
  calc
    9 * ((localProjectedDescentRoot -
          algebraMap Q.K CoefficientCompletion rationalAbscissaTranslation) *
          (9 : CoefficientCompletion)⁻¹) +
        algebraMap Q.K CoefficientCompletion rationalAbscissaTranslation =
      (localProjectedDescentRoot -
          algebraMap Q.K CoefficientCompletion rationalAbscissaTranslation) *
          ((9 : CoefficientCompletion)⁻¹ * 9) +
        algebraMap Q.K CoefficientCompletion rationalAbscissaTranslation := by
          ring
    _ = localProjectedDescentRoot -
          algebraMap Q.K CoefficientCompletion rationalAbscissaTranslation +
        algebraMap Q.K CoefficientCompletion rationalAbscissaTranslation := by
          rw [inv_mul_cancel₀ h9, mul_one]
    _ = localProjectedDescentRoot := by ring

private theorem localNormalizedA_eq_minimalDerivativeCoefficient :
    (localNormalizedA : CoefficientCompletion) =
      36 * (3 * localProjectedMinimalRoot +
        LocalMinimalDescentCurve.a₂) := by
  rw [localNormalizedA_eq_projectedRoot,
    localProjectedDescentRoot_eq_minimal,
    localMinimalDescentCurve_a₂]
  simp only [rationalAbscissaTranslation, map_add, map_sub, map_mul,
    map_pow, map_ofNat, map_div₀]
  field_simp [coefficientCompletion_four_ne_zero]
  ring

private theorem localNormalizedB_eq_minimalDerivative :
    (localNormalizedB : CoefficientCompletion) =
      1296 * (3 * localProjectedMinimalRoot ^ 2 +
        2 * LocalMinimalDescentCurve.a₂ * localProjectedMinimalRoot +
        LocalMinimalDescentCurve.a₄) := by
  rw [localNormalizedB_eq_projectedDerivative,
    localProjectedDescentRoot_eq_minimal,
    localMinimalDescentCurve_a₂,
    localMinimalDescentCurve_a₄]
  simp only [rationalAbscissaTranslation, map_add, map_sub, map_mul,
    map_pow, map_neg, map_ofNat, map_div₀]
  field_simp [coefficientCompletion_two_ne_zero,
    coefficientCompletion_four_ne_zero]
  linear_combination
    3456 * (algebraMap Q.K CoefficientCompletion Q.tau + 2) *
      localTau_cubic

private theorem localMinimalDerivative_isSquare :
    IsSquare (3 * localProjectedMinimalRoot ^ 2 +
      2 * LocalMinimalDescentCurve.a₂ * localProjectedMinimalRoot +
      LocalMinimalDescentCurve.a₄) := by
  have hB : IsSquare (localNormalizedB : CoefficientCompletion) :=
    field_isSquare_of_integer_isSquare localNormalizedB
      localNormalizedB_isSquare
  obtain ⟨z, hz⟩ := hB
  refine ⟨z / 36, ?_⟩
  calc
    3 * localProjectedMinimalRoot ^ 2 +
          2 * LocalMinimalDescentCurve.a₂ * localProjectedMinimalRoot +
          LocalMinimalDescentCurve.a₄ =
        (localNormalizedB : CoefficientCompletion) / 1296 := by
          rw [localNormalizedB_eq_minimalDerivative]
          have h1296 : (1296 : CoefficientCompletion) ≠ 0 :=
            coefficientCompletion_natCast_ne_zero (by norm_num)
          rw [div_eq_mul_inv]
          symm
          calc
            1296 * (3 * localProjectedMinimalRoot ^ 2 +
                2 * LocalMinimalDescentCurve.a₂ *
                  localProjectedMinimalRoot +
                LocalMinimalDescentCurve.a₄) *
                (1296 : CoefficientCompletion)⁻¹ =
              (3 * localProjectedMinimalRoot ^ 2 +
                2 * LocalMinimalDescentCurve.a₂ *
                  localProjectedMinimalRoot +
                LocalMinimalDescentCurve.a₄) *
                ((1296 : CoefficientCompletion) * 1296⁻¹) := by ring
            _ = 3 * localProjectedMinimalRoot ^ 2 +
                2 * LocalMinimalDescentCurve.a₂ *
                  localProjectedMinimalRoot +
                LocalMinimalDescentCurve.a₄ := by
              rw [mul_inv_cancel₀ h1296, mul_one]
    _ = (z * z) / 1296 := by rw [hz]
    _ = (z / 36) * (z / 36) := by
      field_simp [coefficientCompletion_natCast_ne_zero
        (by norm_num : (36 : ℕ) ≠ 0),
        coefficientCompletion_natCast_ne_zero
          (by norm_num : (1296 : ℕ) ≠ 0)]
      ring

/-- Every point of the base-changed minimal descent curve has square
difference from the selected dyadic two-torsion abscissa. -/
theorem localMinimal_curve_isSquare
    (x y : CoefficientCompletion)
    (hcurve : y ^ 2 = LocalMinimalDescentCurve.f.eval x) :
    IsSquare (x - localProjectedMinimalRoot) := by
  have hroot := localProjectedMinimalRoot_isRoot
  rw [Polynomial.IsRoot, LocalMinimalDescentCurve.eval_f] at hroot
  have hcurve' : y ^ 2 =
      x ^ 3 + LocalMinimalDescentCurve.a₂ * x ^ 2 +
        LocalMinimalDescentCurve.a₄ * x +
          LocalMinimalDescentCurve.a₆ := by
    simpa only [LocalMinimalDescentCurve.eval_f] using hcurve
  let Xn : CoefficientCompletion :=
    36 * (x - localProjectedMinimalRoot)
  let Yn : CoefficientCompletion := 216 * y
  have hnormalized : Yn ^ 2 = Xn *
      (Xn ^ 2 + (localNormalizedA : CoefficientCompletion) * Xn +
        localNormalizedB) := by
    dsimp only [Xn, Yn]
    rw [localNormalizedA_eq_minimalDerivativeCoefficient,
      localNormalizedB_eq_minimalDerivative]
    calc
      (216 * y) ^ 2 = 46656 * y ^ 2 := by ring
      _ = 46656 *
          (x ^ 3 + LocalMinimalDescentCurve.a₂ * x ^ 2 +
            LocalMinimalDescentCurve.a₄ * x +
              LocalMinimalDescentCurve.a₆) := by rw [hcurve']
      _ = 36 * (x - localProjectedMinimalRoot) *
          ((36 * (x - localProjectedMinimalRoot)) ^ 2 +
            36 * (3 * localProjectedMinimalRoot +
              LocalMinimalDescentCurve.a₂) *
                (36 * (x - localProjectedMinimalRoot)) +
            1296 * (3 * localProjectedMinimalRoot ^ 2 +
              2 * LocalMinimalDescentCurve.a₂ *
                localProjectedMinimalRoot +
              LocalMinimalDescentCurve.a₄)) := by
        linear_combination 46656 * hroot
  obtain ⟨z, hz⟩ :=
    normalized_local_curve_isSquare Xn Yn hnormalized
  refine ⟨z / 6, ?_⟩
  dsimp only [Xn] at hz
  calc
    x - localProjectedMinimalRoot =
        (36 * (x - localProjectedMinimalRoot)) / 36 := by
          have h36 : (36 : CoefficientCompletion) ≠ 0 :=
            coefficientCompletion_natCast_ne_zero (by norm_num)
          rw [div_eq_mul_inv]
          symm
          calc
            36 * (x - localProjectedMinimalRoot) *
                (36 : CoefficientCompletion)⁻¹ =
              (x - localProjectedMinimalRoot) *
                ((36 : CoefficientCompletion) * 36⁻¹) := by ring
            _ = x - localProjectedMinimalRoot := by
              rw [mul_inv_cancel₀ h36, mul_one]
    _ = (z * z) / 36 := by rw [hz]
    _ = (z / 6) * (z / 6) := by
      field_simp [coefficientCompletion_natCast_ne_zero
        (by norm_num : (6 : ℕ) ≠ 0),
        coefficientCompletion_natCast_ne_zero
          (by norm_num : (36 : ℕ) ≠ 0)]
      ring

private theorem localMinimalProjection_mk (p : Polynomial CoefficientCompletion) :
    localMinimalProjection (AdjoinRoot.mk LocalMinimalDescentCurve.f p) =
      p.eval localProjectedMinimalRoot := by
  simp only [localMinimalProjection, AdjoinRoot.liftAlgHom_mk,
    Algebra.toRingHom_ofId, Algebra.algebraMap_self,
    Polynomial.eval₂_id]

private theorem localMinimalProjection_sub_genericRoot
    (x : CoefficientCompletion) :
    localMinimalProjection
        (AdjoinRoot.mk LocalMinimalDescentCurve.f (C x - X)) =
      x - localProjectedMinimalRoot := by
  rw [localMinimalProjection_mk]
  simp only [eval_sub, eval_C, eval_X]

private theorem localMinimalProjection_adjusted
    (x : CoefficientCompletion) :
    localMinimalProjection
        (AdjoinRoot.mk LocalMinimalDescentCurve.f
          (C x - X + LocalMinimalDescentCurve.fCofactor x)) =
      x - localProjectedMinimalRoot +
        (LocalMinimalDescentCurve.fCofactor x).eval
          localProjectedMinimalRoot := by
  rw [localMinimalProjection_mk]
  simp only [eval_add, eval_sub, eval_C, eval_X]

private theorem localMinimal_fCofactor_eval_root_eq_zero
    {x : CoefficientCompletion}
    (hx : LocalMinimalDescentCurve.f.eval x = 0)
    (hne : x ≠ localProjectedMinimalRoot) :
    (LocalMinimalDescentCurve.fCofactor x).eval
        localProjectedMinimalRoot = 0 := by
  have hfactor := congrArg (Polynomial.eval localProjectedMinimalRoot)
    (LocalMinimalDescentCurve.f_eq_mul_of_eval_eq_zero hx)
  have hrootEval : LocalMinimalDescentCurve.f.eval
      localProjectedMinimalRoot = 0 := localProjectedMinimalRoot_isRoot
  rw [hrootEval, eval_mul, eval_sub, eval_X, eval_C] at hfactor
  exact (mul_eq_zero.mp hfactor.symm).resolve_right
    (sub_ne_zero.mpr hne.symm)

/-- Square-class projection induced by the selected dyadic factor of the
base-changed minimal descent algebra. -/
noncomputable def localMinimalSquareclassProjection :
    Units.modPow LocalMinimalDescentCurve.A 2 →*
      Units.modPow CoefficientCompletion 2 :=
  Units.modPow.map localMinimalProjection.toMonoidHom 2

private noncomputable instance coefficientCompletion_decidableEq :
    DecidableEq CoefficientCompletion := Classical.decEq _



/-- The generic base-change projection and the explicit compositum
projection induce the same map on square classes. -/
theorem localMinimalSquareclassProjection_comp_localRes :
    localMinimalSquareclassProjection.comp
        (minimalDescentCurve.toAffine.localRes CoefficientCompletion) =
      localRelativeSquareclassProjection.comp
        minimalDescentSquareclassEquiv := by
  apply MonoidHom.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H u =>
      simp only [MonoidHom.comp_apply, localMinimalSquareclassProjection,
        localRelativeSquareclassProjection,
        WeierstrassCurve.Affine.localRes, minimalDescentSquareclassEquiv,
        Units.modPow.map_mk, Units.modPow.congr,
        QuotientGroup.congrRangePowMonoidHom]
      apply congrArg QuotientGroup.mk
      apply Units.ext
      exact DFunLike.congr_fun localMinimalProjection_comp_mapA (u :
        minimalDescentCurve.toAffine.A)

private theorem localMinimalSquareclassProjection_unit_eq_one
    {a : LocalMinimalDescentCurve.A} (ha : IsUnit a)
    (hsquare : IsSquare (localMinimalProjection a)) :
    localMinimalSquareclassProjection
        (ha.unit : Units.modPow LocalMinimalDescentCurve.A 2) = 1 := by
  rw [localMinimalSquareclassProjection, Units.modPow.map_unit,
    Units.modPow.unit_eq_one_iff]
  obtain ⟨z, hz⟩ := hsquare
  refine ⟨z, ?_⟩
  change z ^ 2 = localMinimalProjection a
  simpa only [pow_two] using hz.symm

/-- The selected dyadic factor kills the local `x - T` descent image on
the minimal model, including the adjusted value at two-torsion points. -/
theorem localMinimalSquareclassProjection_μ_eq_one
    (P : LocalMinimalDescentCurve.Point) :
    localMinimalSquareclassProjection
        ((WeierstrassCurve.Affine.μ (W := LocalMinimalDescentCurve))
          (.ofAdd P)) = 1 := by
  classical
  rw [WeierstrassCurve.Affine.μ_apply]
  cases P with
  | zero =>
      change localMinimalSquareclassProjection 1 = 1
      exact map_one localMinimalSquareclassProjection
  | some x y hP =>
      rw [WeierstrassCurve.Affine.μ₀_some]
      have hcurve : y ^ 2 = LocalMinimalDescentCurve.f.eval x :=
        (LocalMinimalDescentCurve.equation_iff_eval_f_eq_sq x y).mp hP.1 |>.symm
      have hxySquare := localMinimal_curve_isSquare x y hcurve
      by_cases hx : LocalMinimalDescentCurve.f.eval x = 0
      · rw [WeierstrassCurve.Affine.μX_of_eval_f_eq_zero hx]
        apply localMinimalSquareclassProjection_unit_eq_one
        by_cases hxa : x = localProjectedMinimalRoot
        · subst x
          rw [localMinimalProjection_adjusted, sub_self, zero_add,
            LocalMinimalDescentCurve.eval_fCofactor_self]
          exact localMinimalDerivative_isSquare
        · rw [localMinimalProjection_adjusted,
            localMinimal_fCofactor_eval_root_eq_zero hx hxa, add_zero]
          exact hxySquare
      · rw [WeierstrassCurve.Affine.μX_of_eval_f_ne_zero hx]
        apply localMinimalSquareclassProjection_unit_eq_one
        rw [localMinimalProjection_sub_genericRoot]
        exact hxySquare

/-- The restriction of every global minimal-model descent class is killed
by the selected dyadic factor projection. -/
theorem localMinimalSquareclassProjection_localRes_μ_eq_one
    (P : minimalDescentCurve.toAffine.Point) :
    localMinimalSquareclassProjection
        (minimalDescentCurve.toAffine.localRes CoefficientCompletion
          ((WeierstrassCurve.Affine.μ
            (W := minimalDescentCurve.toAffine)) (.ofAdd P))) = 1 := by
  classical
  have hnatural := congrArg
    (fun f : Multiplicative minimalDescentCurve.toAffine.Point →*
        Units.modPow LocalMinimalDescentCurve.A 2 => f (.ofAdd P))
    (minimalDescentCurve.toAffine.localRes_comp_μ CoefficientCompletion)
  simp only [MonoidHom.comp_apply,
    AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd] at hnatural
  rw [hnatural]
  exact localMinimalSquareclassProjection_μ_eq_one
    (minimalDescentCurve.toAffine.pointMap CoefficientCompletion P)

end

end MazurTorsion.XOneEighteenDyadicCompletionBridge

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenFinalUnconditional. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Unconditional completion of the `X₁(18)` two-descent

The global dyadic norm kernel has exactly the sixteen explicitly displayed
representatives.  The selected dyadic factor admits only their identity
representative in the local descent image.  Transporting the representatives
back through the checked equivalence with the generic minimal descent algebra
therefore makes the global `x - T` image trivial.

The rank-zero, finite-reduction, and Kubert consumers then give both the full
rational-point classification required by `Challenge.XOneEighteenNoncusp` and
the genuine exact-order-eighteen exclusion.
-/

open scoped WeierstrassCurve.Affine

namespace MazurTorsion.XOneEighteenDescent

noncomputable section

open MazurTorsion.XOneEighteenDyadicCompletionBridge
open MazurTorsion.XOneEighteenDyadicKernelSeparation
open MazurTorsion.XOneEighteenDyadicValuationCertificate
open MazurTorsion.XOneEighteenGlobalKernelEquivalence
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenKernelGeneratorSupport
open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenFinalRankZero
open MazurTorsion.XOneEighteenSelmerSieve
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumberOne















/-- The kernel of the selected dyadic factor projection on the generic
minimal descent squareclass algebra. -/
private def selectedMinimalLocalKernel :
    Subgroup minimalDescentCurve.toAffine.M :=
  (localRelativeSquareclassProjection.comp
    minimalDescentSquareclassEquiv.toMonoidHom).ker

/-- Every global minimal-model descent value satisfies the selected local
condition. -/
private theorem minimalDescentCurve_range_μ_le_selectedMinimalLocalKernel :
    (minimalDescentCurve.toAffine.μ).range ≤ selectedMinimalLocalKernel := by
  rintro _ ⟨P, rfl⟩
  change localRelativeSquareclassProjection
      (minimalDescentSquareclassEquiv
        (minimalDescentCurve.toAffine.μ P)) = 1
  calc
    localRelativeSquareclassProjection
          (minimalDescentSquareclassEquiv
            (minimalDescentCurve.toAffine.μ P)) =
        localMinimalSquareclassProjection
          (minimalDescentCurve.toAffine.localRes CoefficientCompletion
            (minimalDescentCurve.toAffine.μ P)) := by
      exact (DFunLike.congr_fun
        localMinimalSquareclassProjection_comp_localRes
          (minimalDescentCurve.toAffine.μ P)).symm
    _ = 1 := by
      simpa only [ofAdd_toAdd] using
        localMinimalSquareclassProjection_localRes_μ_eq_one P.toAdd









end

end MazurTorsion.XOneEighteenDescent

end

open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open WeierstrassCurve.Affine

private theorem point_compositum_squareclass_eq (x y : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K)
    (h : minimalDescentCurve.toAffine.Nonsingular x y)
    (hv : algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM ≠ 0) :
    minimalDescentSquareclassEquiv
      (WeierstrassCurve.Affine.μ (W := minimalDescentCurve.toAffine)
        (.ofAdd (.some x y h))) =
      fieldSquareclass (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM) hv := by
  have hx : minimalDescentCurve.toAffine.f.eval x ≠ 0 :=
    minimalDescentPolynomial_irreducible.not_isRoot_of_natDegree_ne_one
      (by rw [minimalDescentCurve.toAffine.natDegree_f]; norm_num)
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx]
  change (QuotientGroup.mk
    (Units.mapEquiv minimalDescentAlgebraEquiv.toMulEquiv
      ((isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit)) : Units.modPow MazurTorsion.XOneEighteenTwoDivisionArithmetic.M 2) =
      QuotientGroup.mk (Units.mk0 (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM) hv)
  apply congrArg (fun u : MazurTorsion.XOneEighteenTwoDivisionArithmetic.Mˣ => (QuotientGroup.mk u : Units.modPow MazurTorsion.XOneEighteenTwoDivisionArithmetic.M 2))
  apply Units.ext
  change minimalDescentAlgebraEquiv
    (((isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit) : minimalDescentCurve.toAffine.A) = _
  rw [IsUnit.unit_spec, map_sub, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_sub]
  change minimalDescentAlgebraEquiv
    (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K minimalDescentCurve.toAffine.A x) -
      minimalDescentAlgebraEquiv minimalGenericRoot = _
  rw [minimalDescentAlgebraEquiv.commutes, minimalDescentAlgebraEquiv_genericRoot]
  simp only [Units.val_mk0]

open MazurTorsion.XOneEighteenDescent

theorem solution (x y : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K)
    (h : minimalDescentCurve.toAffine.Nonsingular x y)
    (hv : algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K
      MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM ≠ 0) :
    MazurTorsion.XOneEighteenDyadicCompletionBridge.localRelativeSquareclassProjection
      (fieldSquareclass (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K
        MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM) hv) = 1 := by
  have hl : WeierstrassCurve.Affine.μ (W := minimalDescentCurve.toAffine)
      (.ofAdd (.some x y h)) ∈ selectedMinimalLocalKernel :=
    minimalDescentCurve_range_μ_le_selectedMinimalLocalKernel
      ⟨.ofAdd (.some x y h), rfl⟩
  change MazurTorsion.XOneEighteenDyadicCompletionBridge.localRelativeSquareclassProjection
    (minimalDescentSquareclassEquiv
      (WeierstrassCurve.Affine.μ (W := minimalDescentCurve.toAffine)
        (.ofAdd (.some x y h)))) = 1 at hl
  rw [point_compositum_squareclass_eq x y h hv] at hl
  exact hl
#print axioms solution
