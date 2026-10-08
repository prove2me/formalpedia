-- Prove2me | solution 1 for MazurTransfer.order18_original_global_norm_kernel_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T15:48:24.72257+00:00
-- url     : https://prove2.me/submissions/858dff00-b9d1-408c-8a55-1e0c2e6391e7

import Mathlib
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

namespace MazurTorsion.XOneEighteenDyadicKernelSeparation
theorem kernelRepresentative_injective : Function.Injective
    MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative :=
  MazurTransfer.order18_original_kernel_representative_injective
end MazurTorsion.XOneEighteenDyadicKernelSeparation

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralModel
end MazurTorsion.XOneEighteenTwoDivisionIntegralModel


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
lemma pow_eq_one {n : ℕ} (m : Units.modPow α n) : m ^ n = 1 := by
  obtain ⟨u, rfl⟩ := mk'_surjective _ m
  rw [mk'_apply, ← mk_pow]
  exact (mk_eq_one_iff n).mpr ⟨u, rfl⟩







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



/-- If a product of two integral elements is a unit, then each factor is a unit. -/
lemma Valuation.eq_one_of_mul_eq_one (ha : ν a ≤ 1) (hb : ν b ≤ 1) (hab : ν (a * b) = 1) :
    ν a = 1 := by
  refine le_antisymm ha ?_
  calc (1 : Γ) = ν a * ν b := by rw [← map_mul, hab]
    _ ≤ ν a * 1 := by gcongr
    _ = ν a := mul_one _





end Valuation

section DedekindDomain

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]











/-- The `Multiplicative ℤ`-valued valuation of a unit is determined by the `ℤᵐ⁰`-valued one. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZero_eq_iff (v : HeightOneSpectrum R)
    (u : Kˣ) (m : Multiplicative ℤ) :
    v.valuationOfNeZero u = m ↔ v.valuation K (u : K) = (m : WithZero (Multiplicative ℤ)) := by
  rw [← WithZero.coe_inj, valuationOfNeZero_eq]



/-- The class of a unit `u` in `Units.modPow K n` has trivial image under the `v`-adic valuation
mod `n` exactly when the `v`-adic valuation of `u` is divisible by `n`. -/
lemma IsDedekindDomain.HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (u : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk u) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero u) := by
  erw [valuationOfNeZeroMod, MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe,
    MonoidHom.coe_coe, EmbeddingLike.map_eq_one_iff]
  refine (QuotientGroup.eq_one_iff _).trans ?_
  rw [Multiplicative.mem_toSubgroup, AddSubgroup.mem_zmultiples_iff]
  exact ⟨fun ⟨k, hk⟩ ↦ ⟨k, by rw [← hk]; ring⟩, fun ⟨k, hk⟩ ↦ ⟨k, by rw [hk]; ring⟩⟩







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



instance IsDedekindDomain.HeightOneSpectrum.instLiesOverBelow [Algebra.IsIntegral R B]
    (w : HeightOneSpectrum B) :
    w.asIdeal.LiesOver (w.below R).asIdeal :=
  Ideal.over_under ..

lemma IsDedekindDomain.HeightOneSpectrum.mem_primesAbove_iff [Algebra.IsIntegral R B]
    (S : Set (HeightOneSpectrum R)) (w : HeightOneSpectrum B) :
    w ∈ primesAbove R B S ↔ w.below R ∈ S := by
  refine ⟨fun ⟨v, hv, hva⟩ ↦ ?_, fun hw ↦ ⟨w.below R, hw, rfl⟩⟩
  rwa [show w.below R = v from HeightOneSpectrum.ext hva.symm]







-- as for `mem_selmerGroupAbove_iff`, the instances are needed for the statement only


namespace IsDiscreteValuationRing

variable (A : Type*) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]



variable {A}



end IsDiscreteValuationRing

namespace IsDedekindDomain.HeightOneSpectrum

variable {B C : Type*} [CommRing B] [IsDedekindDomain B] [CommRing C] [IsDedekindDomain C]

/-- The height-one prime of `B` obtained by contracting a height-one prime along a ring
homomorphism `ψ : B →+* C`, given that the contraction is nonzero. -/
def comapOfNeBot (ψ : B →+* C) (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    HeightOneSpectrum B where
  asIdeal := w.asIdeal.comap ψ
  isPrime := w.isPrime.comap ψ
  ne_bot := hne

-- the `IsDedekindDomain` instances are needed to state this, but the proof (`rfl`) erases them


variable {L N : Type*} [Field L] [Algebra B L] [IsFractionRing B L]
  [Field N] [Algebra C N] [IsFractionRing C N]

/-- The `w`-adic valuation of `φ u` is the valuation of `u` at the contracted prime, raised
to a fixed positive power (the ramification index), for an embedding `φ` of fraction fields
compatible with an embedding `ψ` of Dedekind domains. -/
theorem exists_valuationOfNeZero_map_eq (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) :
    ∃ e : ℕ, ∀ u : Lˣ, w.valuationOfNeZero (Units.map (φ : L →* N) u) =
      (comapOfNeBot ψ w hne).valuationOfNeZero u ^ e := by
  let _ : Algebra B C := ψ.toAlgebra
  let _ : Algebra L N := φ.toAlgebra
  let _ : Algebra B N := (φ.comp (algebraMap B L)).toAlgebra
  have hψ : Function.Injective ψ := by
    have h : Function.Injective ((algebraMap C N).comp ψ) := by
      rw [hcomp]
      exact φ.injective.comp (IsFractionRing.injective B L)
    exact fun x y hxy ↦ h (by simp only [RingHom.comp_apply, hxy])
  have ht1 : IsScalarTower B L N := .of_algebraMap_eq' rfl
  have ht2 : IsScalarTower B C N := .of_algebraMap_eq fun x ↦ (RingHom.congr_fun hcomp x).symm
  have htf : Module.IsTorsionFree B C := Module.isTorsionFree_iff_algebraMap_injective.mpr hψ
  have hlie : w.asIdeal.LiesOver (comapOfNeBot ψ w hne).asIdeal := ⟨rfl⟩
  refine ⟨(comapOfNeBot ψ w hne).asIdeal.ramificationIdx' w.asIdeal, fun u ↦ ?_⟩
  rw [valuationOfNeZero_eq_iff, WithZero.coe_pow, valuationOfNeZero_eq, Units.coe_map,
    MonoidHom.coe_coe]
  exact (valuation_liesOver N (comapOfNeBot ψ w hne) w (u : L)).symm

/-- Divisibility of adic valuations transports along compatible embeddings: if the valuation
of `u` at the contracted prime is divisible by `n`, so is the `w`-adic valuation of `φ u`. -/
theorem dvd_toAdd_valuationOfNeZero_map (φ : L →+* N) (ψ : B →+* C)
    (hcomp : (algebraMap C N).comp ψ = φ.comp (algebraMap B L))
    (w : HeightOneSpectrum C) (hne : w.asIdeal.comap ψ ≠ ⊥) {n : ℕ} (u : Lˣ)
    (h : (n : ℤ) ∣ Multiplicative.toAdd ((comapOfNeBot ψ w hne).valuationOfNeZero u)) :
    (n : ℤ) ∣ Multiplicative.toAdd (w.valuationOfNeZero (Units.map (φ : L →* N) u)) := by
  obtain ⟨e, he⟩ := exists_valuationOfNeZero_map_eq φ ψ hcomp w hne
  rw [he u, toAdd_pow, nsmul_eq_mul]
  exact h.mul_left _



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





/-- Closed formula for the relative norm of a quadratic representative.
This is the determinant of multiplication in the basis `1,s,s²`. -/
theorem norm_quadraticElement (a b c : Q.K) :
    Algebra.norm Q.K (quadraticElement a b c) =
      100 * a ^ 3 - 30 * a ^ 2 * b + 9 * a ^ 2 * c -
        30 * a * b * c + 6 * a * c ^ 2 + 10 * b ^ 3 -
        3 * b ^ 2 * c + c ^ 3 := by
  let pb := AdjoinRoot.powerBasis' relativePolynomial_monic
  rw [quadraticElement_eq, Algebra.norm_eq_matrix_det pb.basis]
  simp only [map_add, map_mul, map_pow]
  rw [(Algebra.leftMulMatrix pb.basis).commutes a,
    (Algebra.leftMulMatrix pb.basis).commutes b,
    (Algebra.leftMulMatrix pb.basis).commutes c]
  have hs : s = pb.gen := rfl
  rw [hs, pb.leftMulMatrix]
  have hmin : pb.minpolyGen = relativePolynomial := by
    dsimp [pb]
    rw [PowerBasis.minpolyGen_eq,
      AdjoinRoot.powerBasis'_gen,
      AdjoinRoot.minpoly_root relativePolynomial_monic.ne_zero,
      relativePolynomial_monic.leadingCoeff, inv_one, C_1, mul_one]
  rw [hmin]
  have hdim : pb.dim = 3 := relativePolynomial_natDegree
  let e : Fin pb.dim ≃ Fin 3 := finCongr hdim
  let companion : Matrix (Fin pb.dim) (Fin pb.dim) Q.K :=
    fun i j ↦ if (j : ℕ) + 1 = pb.dim then
      -relativePolynomial.coeff i
    else if (i : ℕ) = j + 1 then 1 else 0
  change Matrix.det
    (algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) a *
          companion ^ 2 +
        algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) b *
          companion +
      algebraMap Q.K (Matrix (Fin pb.dim) (Fin pb.dim) Q.K) c) = _
  have hcompanion :
      Matrix.reindexAlgEquiv Q.K Q.K e companion =
        !![0, 0, 10; 1, 0, 3; 0, 1, 0] := by
    ext i j
    change companion (e.symm i) (e.symm j) = _
    fin_cases i <;> fin_cases j <;>
      simp [companion, e, hdim, relativePolynomial, coeff_sub,
        coeff_X_pow, coeff_X]
  conv_lhs => rw [← Matrix.det_reindexAlgEquiv Q.K (R := Q.K) e]
  rw [map_add, map_add, map_mul, map_pow, map_mul]
  rw [(Matrix.reindexAlgEquiv Q.K Q.K e).commutes a,
    (Matrix.reindexAlgEquiv Q.K Q.K e).commutes b,
    (Matrix.reindexAlgEquiv Q.K Q.K e).commutes c]
  rw [hcompanion]
  rw [Matrix.det_fin_three]
  simp [Matrix.algebraMap_matrix_apply, Matrix.mul_apply, pow_two]
  ring















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

private theorem tau_pow_four : Q.tau ^ 4 = 3 * Q.tau ^ 2 + Q.tau := by
  calc
    Q.tau ^ 4 = Q.tau * Q.tau ^ 3 := by ring
    _ = Q.tau * (3 * Q.tau + 1) := by rw [Q.tau_cubic]
    _ = 3 * Q.tau ^ 2 + Q.tau := by ring

private theorem tau_pow_five :
    Q.tau ^ 5 = Q.tau ^ 2 + 9 * Q.tau + 3 := by
  calc
    Q.tau ^ 5 = Q.tau * Q.tau ^ 4 := by ring
    _ = Q.tau * (3 * Q.tau ^ 2 + Q.tau) := by rw [tau_pow_four]
    _ = 3 * Q.tau ^ 3 + Q.tau ^ 2 := by ring
    _ = Q.tau ^ 2 + 9 * Q.tau + 3 := by rw [Q.tau_cubic]; ring

private theorem tau_pow_six :
    Q.tau ^ 6 = 9 * Q.tau ^ 2 + 6 * Q.tau + 1 := by
  calc
    Q.tau ^ 6 = (Q.tau ^ 3) ^ 2 := by ring
    _ = (3 * Q.tau + 1) ^ 2 := by rw [Q.tau_cubic]
    _ = 9 * Q.tau ^ 2 + 6 * Q.tau + 1 := by ring







/-- The first kernel representative has relative norm one. -/
theorem norm_h1 : Algebra.norm Q.K h1 = 1 := by
  rw [h1, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

/-- The second kernel representative has relative norm one. -/
theorem norm_h2 : Algebra.norm Q.K h2 = 1 := by
  rw [h2, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

/-- The third kernel representative has relative norm four. -/
theorem norm_h3 : Algebra.norm Q.K h3 = 4 := by
  rw [h3, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_four, Q.tau_cubic]
  ring

/-- The fourth kernel representative has the displayed quadratic norm. -/
theorem norm_h4 :
    Algebra.norm Q.K h4 = 4 * (-Q.tau ^ 2 + Q.tau + 4) := by
  rw [h4, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_four]
  ring

/-- The coefficient occurring in `norm_h4` is the advertised square after
using the coefficient cubic relation. -/
theorem four_mul_neg_tau_sq_add_tau_add_four_eq_square :
    4 * (-Q.tau ^ 2 + Q.tau + 4) = (2 * (Q.tau ^ 2 - 2)) ^ 2 := by
  rw [show (2 * (Q.tau ^ 2 - 2)) ^ 2 =
    4 * Q.tau ^ 4 - 16 * Q.tau ^ 2 + 16 by ring, tau_pow_four]
  ring

/-- The norm of `h4`, in a form immediately usable by squareclass code. -/
theorem norm_h4_eq_square :
    Algebra.norm Q.K h4 = (2 * (Q.tau ^ 2 - 2)) ^ 2 := by
  rw [norm_h4, four_mul_neg_tau_sq_add_tau_add_four_eq_square]



end

end MazurTorsion.XOneEighteenTwoDivisionArithmetic

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

/-- The integral polynomial `X³ - 3X - 1`. -/
def coefficientPolynomialInt : Polynomial ℤ := X ^ 3 - 3 * X - 1

theorem coefficientPolynomialInt_monic : coefficientPolynomialInt.Monic := by
  simp only [coefficientPolynomialInt]
  monicity <;> norm_num



private theorem coefficientPolynomialInt_aeval_tau :
    Polynomial.aeval Q.tau coefficientPolynomialInt = 0 := by
  simp only [coefficientPolynomialInt, map_sub, map_pow, aeval_X,
    map_mul, map_ofNat, map_one]
  linear_combination Q.tau_cubic

/-- The coefficient-field generator as an algebraic integer. -/
def coefficientInteger : 𝓞 Q.K :=
  ⟨Q.tau, ⟨coefficientPolynomialInt, coefficientPolynomialInt_monic,
    coefficientPolynomialInt_aeval_tau⟩⟩

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

def coefficientPolynomialMod (p : ℕ) : Polynomial (ZMod p) :=
  X ^ 3 - 3 * X - 1



theorem coefficientPolynomialInt_map_zmod (p : ℕ) :
    coefficientPolynomialInt.map (Int.castRingHom (ZMod p)) =
      coefficientPolynomialMod p := by
  norm_num [coefficientPolynomialInt, coefficientPolynomialMod]











































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


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionIntegralModel. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The integral normalized model of the `X₁(18)` two-division compositum

This file records the integer polynomial underlying the normalized rational
power basis and lifts its generator to the full ring of integers.  It makes
no claim that the resulting order is the maximal order.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionIntegralModel

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

/-- The monic integer polynomial underlying `normalizedPolynomial`. -/
def normalizedPolynomialInt : Polynomial ℤ :=
  X ^ 9 - 3 * X ^ 8 + 7 * X ^ 6 - 3 * X ^ 5 - 9 * X ^ 4 +
    3 * X ^ 3 + 6 * X ^ 2 - 1

theorem normalizedPolynomialInt_monic : normalizedPolynomialInt.Monic := by
  simp only [normalizedPolynomialInt]
  monicity <;> norm_num





theorem normalizedPolynomialInt_aeval :
    Polynomial.aeval normalizedElement normalizedPolynomialInt = 0 := by
  simpa only [normalizedPolynomialInt, normalizedPolynomial, map_add, map_sub,
    map_mul, map_pow, map_ofNat, map_one, aeval_X] using
      normalizedElement_root

/-- The normalized generator is an algebraic integer. -/
theorem normalizedElement_isIntegral_int :
    IsIntegral ℤ normalizedElement :=
  ⟨normalizedPolynomialInt, normalizedPolynomialInt_monic,
    normalizedPolynomialInt_aeval⟩











end

end MazurTorsion.XOneEighteenTwoDivisionIntegralModel

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


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionPrincipalSmallPrimes. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Principal ideals above the small ramified primes in the `X₁(18)` compositum

The integral quotients constructed in
`XOneEighteenTwoDivisionIntegralElements` are units.  This is verified by
explicit integral Bezout inverses modulo the normalized degree-nine
polynomial.  Consequently the advertised element factorizations give exact
ideal identities

`(2) = (alpha) * (beta)^2` and `(3) = (rho)^3`.

No maximal-order assertion about the normalized power order is used.
-/

open Polynomial Module NumberField

namespace MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open NumberField Ideal RingOfIntegers UniqueFactorizationMonoid

/-! ## Explicit inverses for the two integral quotients -/





























/-! ## Exact principal-ideal factorizations -/









/-! ## Absolute norms of the three generators -/













/-! ## Dyadic inertia -/

local instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

theorem coefficientPolynomialMod_two_irreducible :
    Irreducible (coefficientPolynomialMod 2) := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · have hdegree : (coefficientPolynomialMod 2).natDegree = 3 := by
      simp only [coefficientPolynomialMod]
      compute_degree!
    rw [hdegree]
    norm_num
  · intro z
    unfold Polynomial.IsRoot
    simp only [coefficientPolynomialMod, eval_sub, eval_pow, eval_X,
      eval_mul, eval_ofNat, eval_one]
    fin_cases z <;> decide

private theorem coefficient_exponent_not_dvd_two :
    ¬ 2 ∣ RingOfIntegers.exponent coefficientInteger := by
  rw [RingOfIntegers.not_dvd_exponent_iff]
  have hspan : Ideal.span {(81 : ℤ)} ≤
      Ideal.comap (algebraMap ℤ (NumberField.RingOfIntegers Q.K))
        (conductor ℤ coefficientInteger) := by
    rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap]
    exact coefficient_discriminant_mem_conductor
  exact ((Ideal.isCoprime_span_singleton_iff (81 : ℤ) (2 : ℤ)).mpr
    (by norm_num)).codisjoint.mono_left hspan

theorem coefficient_inertiaDeg_eq_three_at_two
    (P : Ideal (NumberField.RingOfIntegers Q.K))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers Q.K)) :
    P.inertiaDeg ℤ = 3 := by
  have hirr : Irreducible
      ((minpoly ℤ coefficientInteger).map (Int.castRingHom (ZMod 2))) := by
    rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod]
    exact coefficientPolynomialMod_two_irreducible
  let e := NumberField.Ideal.primesOverSpanEquivMonicFactorsMod
    coefficient_exponent_not_dvd_two
  have hfactor := (e ⟨P, hP⟩).2
  have hdegree :=
    NumberField.Ideal.inertiaDeg_primesOverSpanEquivMonicFactorsMod_symm_apply'
      coefficient_exponent_not_dvd_two hfactor
  simp only [Subtype.coe_eta] at hdegree
  change (e ⟨P, hP⟩ : Polynomial (ZMod 2)) ∈
      (normalizedFactors
        ((minpoly ℤ coefficientInteger).map
          (Int.castRingHom (ZMod 2)))).toFinset at hfactor
  rw [normalizedFactors_irreducible hirr,
    (minpoly.monic coefficientInteger.isIntegral).map
      (Int.castRingHom (ZMod 2)) |>.normalize_eq_self] at hfactor
  simp only [Multiset.toFinset_singleton, Finset.mem_singleton] at hfactor
  rw [hfactor] at hdegree
  have heq := e.symm_apply_apply ⟨P, hP⟩
  have hideal : ((e.symm (e ⟨P, hP⟩)).1 :
      Ideal (NumberField.RingOfIntegers Q.K)) = P :=
    congrArg Subtype.val heq
  rw [hideal] at hdegree
  rw [coefficientInteger_minpoly, coefficientPolynomialInt_map_zmod] at hdegree
  have hnatDegree : (coefficientPolynomialMod 2).natDegree = 3 := by
    simp only [coefficientPolynomialMod]
    compute_degree!
  exact hdegree.trans hnatDegree









end

end MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes

end


/- Source module: MazurTorsion.NumberTheory.UnramifiedArtin. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# The unramified ideal Artin map

This file develops the part of the ideal-theoretic Artin map that follows from
Dedekind factorization and local Frobenius theory.  For a finite Galois
extension of number fields it chooses a prime above every finite prime and
defines the corresponding arithmetic Frobenius.  In an abelian extension the
choice disappears, since Frobenius elements above the same prime are
conjugate.  The local symbols then extend uniquely to a homomorphism from the
group of nonzero fractional ideals.

The construction here is deliberately separate from global reciprocity.  The
two global assertions needed later are that principal ideals lie in the
kernel, and that the resulting Artin map is onto.  Neither assertion is used
in this file.

The divisor equivalence below is the scheme-free Dedekind-domain core of the
construction in Tau Ceti's
`AlgebraicGeometry/WeilDivisor/FractionalIdealDivisor/Basic.lean`; it is
reproved here directly from Mathlib's fractional-ideal factorization API so
this number-theory module does not depend on Picard or Weil-divisor theory.
-/

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped IsMulCommutative NumberField nonZeroDivisors Pointwise

namespace NumberTheory.UnramifiedArtin

attribute [local instance] Ideal.Quotient.field

universe u v w w'



section LocalDecompositionGroup

variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [Group G] [Finite G] [MulSemiringAction G S] [SMulCommClass G R S]
variable [IsGaloisGroup G R S] [IsDomain R] [IsDomain S]
variable [Module.Finite R S] [Module.Flat R S]



end LocalDecompositionGroup

section Frobenius

variable {K : Type u} {L : Type v} [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [IsGalois K L]











end Frobenius

section SemilinearFrobenius

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]
variable [Algebra R S]













end SemilinearFrobenius

section FractionalIdeals

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]



/-- The finitely supported multiplicity divisor of an invertible fractional
ideal. -/
noncomputable def fractionalIdealDivisor :
    Additive (FractionalIdeal R⁰ K)ˣ →+ (HeightOneSpectrum R →₀ ℤ) where
  toFun I := Finsupp.ofSupportFinite
    (fun x => FractionalIdeal.count K x (Units.val (Additive.toMul I)))
    (by
      simpa only [Function.support] using Filter.eventually_cofinite.mp
        (FractionalIdeal.finite_factors (Units.val (Additive.toMul I))))
  map_zero' := by
    apply Finsupp.ext
    intro x
    rw [Finsupp.ofSupportFinite_coe]
    simp only [toMul_zero, Units.val_one, Finsupp.coe_zero, Pi.zero_apply]
    exact FractionalIdeal.count_one K x
  map_add' I J := by
    apply Finsupp.ext
    intro x
    rw [Finsupp.add_apply, Finsupp.ofSupportFinite_coe,
      Finsupp.ofSupportFinite_coe, Finsupp.ofSupportFinite_coe]
    simp only [toMul_add, Units.val_mul]
    exact FractionalIdeal.count_mul K x (Units.ne_zero _) (Units.ne_zero _)

/-- The coefficient of the fractional-ideal divisor is Mathlib's local
multiplicity. -/
@[simp]
theorem fractionalIdealDivisor_apply
    (I : Additive (FractionalIdeal R⁰ K)ˣ) (x : HeightOneSpectrum R) :
    fractionalIdealDivisor R K I x =
      FractionalIdeal.count K x (Units.val (Additive.toMul I)) := by
  simp only [fractionalIdealDivisor, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Finsupp.ofSupportFinite_coe]

/-- A nonzero fractional ideal is recovered from all of its finite-prime
multiplicities. -/
theorem fractionalIdealDivisor_injective :
    Function.Injective (fractionalIdealDivisor R K) := by
  intro I J h
  have hcount : ∀ x,
      FractionalIdeal.count K x (Units.val (Additive.toMul I)) =
        FractionalIdeal.count K x (Units.val (Additive.toMul J)) := by
    intro x
    have hx := DFunLike.congr_fun h x
    simpa using hx
  have hval : Units.val (Additive.toMul I) =
      Units.val (Additive.toMul J) := by
    rw [← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
          (Units.ne_zero (Additive.toMul I)),
      ← FractionalIdeal.finprod_heightOneSpectrum_factorization' K
          (Units.ne_zero (Additive.toMul J))]
    exact finprod_congr fun x => by rw [hcount x]
  exact Additive.toMul.injective (Units.ext hval)

/-- The fractional ideal attached to a finitely supported integer divisor is
nonzero. -/
theorem prod_asIdeal_zpow_ne_zero (D : HeightOneSpectrum R →₀ ℤ) :
    (D.prod fun x e => (x.asIdeal : FractionalIdeal R⁰ K) ^ e) ≠ 0 := by
  rw [Finsupp.prod]
  exact Finset.prod_ne_zero_iff.mpr fun x _ =>
    zpow_ne_zero _ (FractionalIdeal.coeIdeal_ne_zero.mpr x.ne_bot)

/-- Every finitely supported integer divisor is the divisor of a nonzero
fractional ideal. -/
theorem fractionalIdealDivisor_surjective :
    Function.Surjective (fractionalIdealDivisor R K) := by
  intro D
  refine ⟨Additive.ofMul (Units.mk0
    (D.prod fun x e => (x.asIdeal : FractionalIdeal R⁰ K) ^ e)
    (prod_asIdeal_zpow_ne_zero R K D)), ?_⟩
  apply Finsupp.ext
  intro x
  rw [fractionalIdealDivisor_apply]
  simp only [toMul_ofMul, Units.val_mk0]
  exact FractionalIdeal.count_finsuppProd K x D

/-- Nonzero fractional ideals form the free abelian group on the finite
primes of a Dedekind domain. -/
noncomputable def fractionalIdealDivisorAddEquiv :
    Additive (FractionalIdeal R⁰ K)ˣ ≃+ (HeightOneSpectrum R →₀ ℤ) :=
  AddEquiv.ofBijective (fractionalIdealDivisor R K)
    ⟨fractionalIdealDivisor_injective R K,
      fractionalIdealDivisor_surjective R K⟩

variable {R K}



variable {M : Type w} [CommGroup M]

/-- The multiplicative form of the divisor equivalence for nonzero
fractional ideals. -/
noncomputable def fractionalIdealDivisorMulEquiv :
    (FractionalIdeal R⁰ K)ˣ ≃* Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  (fractionalIdealDivisorAddEquiv R K).toMultiplicativeRight













variable {N : Type w'} [CommGroup N]















end FractionalIdeals

section ClassGroup

variable (R : Type u) [CommRing R] [IsDedekindDomain R]
variable (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]
variable {M : Type w} [CommGroup M]



















end ClassGroup

section Artin

variable {K : Type u} {L : Type v} [Field K] [NumberField K]
variable [Field L] [NumberField L] [Algebra K L] [IsGalois K L]





end Artin

end NumberTheory.UnramifiedArtin

end


/- Source module: MazurTorsion.NumberTheory.SelmerClassGroup. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Empty-support Selmer groups and ideal-class torsion

For a Dedekind domain `R` with fraction field `K` and a positive natural
number `n`, this file constructs the canonical homomorphism

`K⟮∅, n⟯ → ClassGroup R[n]`.

A representative has principal divisor divisible coefficientwise by `n`.
Dividing that divisor and using the free-abelian description of nonzero
fractional ideals gives an `n`-th root ideal. Its ideal class is independent
of the representative. The construction is formalized first on the preimage
of the Selmer group in `Kˣ`, then descended through actual `n`-th powers.

The kernel is proved to be exactly the image of integral units modulo
`n`-th powers, and the map onto class-group torsion is proved surjective.
Thus this file formalizes the short exact sequence

`Rˣ/(Rˣ)^n → K⟮∅, n⟯ → ClassGroup R[n] → 1`.

This is ideal-theoretic and uses no global reciprocity or class-field-theory
existence theorem. The construction is also proved natural under ring
automorphisms of `R`, acting through the induced automorphisms of `K`, the
empty-support Selmer group, and the ideal class group.
-/


open scoped nonZeroDivisors

namespace IsDedekindDomain.selmerGroup

noncomputable section

universe u v

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The exponent of a principal fractional ideal is the negative logarithm
of the normalized finite-place valuation. -/
theorem count_spanSingleton_eq_neg_valuationLog
    (a : K) (ha : a ≠ 0) (v : HeightOneSpectrum R) :
    FractionalIdeal.count K v
      (FractionalIdeal.spanSingleton R⁰ a) =
      -WithZero.log (v.valuation K a) := by
  let x : Kˣ := Units.mk0 a ha
  let s := IsLocalization.sec R⁰ (x : K)
  have hs : IsLocalization.mk' K s.1 s.2 = x :=
    IsLocalization.mk'_sec K x
  have hI : FractionalIdeal.spanSingleton R⁰ (x : K) =
      FractionalIdeal.spanSingleton R⁰
          ((algebraMap R K) (s.2 : R))⁻¹ *
        (Ideal.span {s.1} : Ideal R) := by
    rw [FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_mul_spanSingleton]
    apply congrArg
    rw [← hs, IsFractionRing.mk'_eq_div, div_eq_mul_inv, mul_comm]
  have hcount := FractionalIdeal.count_well_defined K v
    (FractionalIdeal.spanSingleton_ne_zero_iff.mpr ha) hI
  have hval := congrArg WithZero.log
    (HeightOneSpectrum.valuationOfNeZeroToFun_eq v x)
  dsimp only [HeightOneSpectrum.valuationOfNeZeroToFun, x, s] at hval hcount ⊢
  simp only [Units.val_mk0] at hval hcount ⊢
  change
    (-((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span
            {(IsLocalization.sec R⁰ a).1})).factors : ℤ) -
      -((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span
            {((IsLocalization.sec R⁰ a).2 : R)})).factors : ℤ)) =
        WithZero.log (v.valuation K a) at hval
  rw [hcount]
  omega

theorem valuationOfNeZeroMod_mk_eq_one_iff
    (v : HeightOneSpectrum R) (n : ℕ) (x : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 ↔
      (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) := by
  erw [HeightOneSpectrum.valuationOfNeZeroMod, MonoidHom.comp_apply,
    ← QuotientGroup.coe_mk', QuotientGroup.map_mk']
  constructor
  · intro h
    have hq := (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative.injective
      (h.trans (map_one
        (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative).symm)
    have hm := (QuotientGroup.eq_one_iff
      (v.valuationOfNeZero x)).mp hq
    change Multiplicative.toAdd (v.valuationOfNeZero x) ∈
      AddSubgroup.zmultiples (n : ℤ) at hm
    rw [AddSubgroup.mem_zmultiples_iff] at hm
    rcases hm with ⟨k, hk⟩
    refine ⟨k, ?_⟩
    simpa [mul_comm] using hk.symm
  · rintro ⟨k, hk⟩
    have hm : Multiplicative.toAdd (v.valuationOfNeZero x) ∈
        AddSubgroup.zmultiples (n : ℤ) := by
      rw [AddSubgroup.mem_zmultiples_iff]
      exact ⟨k, by simpa [mul_comm] using hk.symm⟩
    change v.valuationOfNeZero x ∈
      AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ)) at hm
    have hq := (QuotientGroup.eq_one_iff
      (v.valuationOfNeZero x)).mpr hm
    have he := congrArg
      (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative hq
    exact he.trans (map_one
      (Int.quotientZMultiplesNatEquivZMod n).toMultiplicative)

open NumberTheory.UnramifiedArtin

/-- The finitely supported divisor of a nonzero field element, obtained from
its principal fractional ideal. -/
noncomputable def principalDivisor :
    Kˣ →* Multiplicative (HeightOneSpectrum R →₀ ℤ) :=
  (fractionalIdealDivisor R K).toMultiplicativeRight.comp
    (toPrincipalIdeal R K)

@[simp]
theorem principalDivisor_apply (x : Kˣ) (v : HeightOneSpectrum R) :
    Multiplicative.toAdd (principalDivisor (R := R) (K := K) x) v =
      -Multiplicative.toAdd (v.valuationOfNeZero x) := by
  have hval := congrArg WithZero.log
    (HeightOneSpectrum.valuationOfNeZero_eq v x)
  change Multiplicative.toAdd (v.valuationOfNeZero x) =
    WithZero.log (v.valuation K (x : K)) at hval
  unfold principalDivisor
  change fractionalIdealDivisor R K
      (Additive.ofMul (toPrincipalIdeal R K x)) v = _
  rw [fractionalIdealDivisor_apply]
  simp only [toMul_ofMul, coe_toPrincipalIdeal]
  rw [count_spanSingleton_eq_neg_valuationLog (x : K) x.ne_zero v]
  exact congrArg Neg.neg hval.symm

/-- Representatives in `Kˣ` whose classes satisfy all empty-support
Selmer local conditions. -/
def preSelmer (n : ℕ) : Subgroup Kˣ :=
  Subgroup.comap
    (QuotientGroup.mk'
      (powMonoidHom n : Kˣ →* Kˣ).range)
    (selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n))

/-- Every coefficient of the principal divisor of a pre-Selmer
representative is divisible by `n`. -/
theorem principalDivisor_coeff_dvd (n : ℕ)
    (x : preSelmer (R := R) (K := K) n)
    (v : HeightOneSpectrum R) :
    (n : ℤ) ∣
      Multiplicative.toAdd
        (principalDivisor (R := R) (K := K) (x : Kˣ)) v := by
  have hlocal : v.valuationOfNeZeroMod n
      (QuotientGroup.mk (x : Kˣ)) = 1 :=
    x.property v (Set.notMem_empty v)
  have hv := (valuationOfNeZeroMod_mk_eq_one_iff v n (x : Kˣ)).mp hlocal
  rw [principalDivisor_apply]
  exact dvd_neg.mpr hv

/-- Divide the principal divisor of a pre-Selmer representative
coefficientwise by `n`. -/
noncomputable def rootDivisor (n : ℕ)
    (x : preSelmer (R := R) (K := K) n) :
    HeightOneSpectrum R →₀ ℤ :=
  Finsupp.mapRange (fun z : ℤ => z / (n : ℤ)) (by simp)
    (Multiplicative.toAdd
      (principalDivisor (R := R) (K := K) (x : Kˣ)))

@[simp]
theorem rootDivisor_apply (n : ℕ)
    (x : preSelmer (R := R) (K := K) n)
    (v : HeightOneSpectrum R) :
    rootDivisor (R := R) (K := K) n x v =
      Multiplicative.toAdd
        (principalDivisor (R := R) (K := K) (x : Kˣ)) v / (n : ℤ) := by
  rfl

theorem rootDivisor_one (n : ℕ) :
    rootDivisor (R := R) (K := K) n 1 = 0 := by
  ext v
  simp [rootDivisor]

theorem rootDivisor_mul (n : ℕ)
    (x y : preSelmer (R := R) (K := K) n) :
    rootDivisor (R := R) (K := K) n (x * y) =
      rootDivisor (R := R) (K := K) n x +
        rootDivisor (R := R) (K := K) n y := by
  ext v
  simp only [rootDivisor_apply, Subgroup.coe_mul, map_mul,
    toAdd_mul, Finsupp.add_apply]
  exact Int.add_ediv_of_dvd_left
    (principalDivisor_coeff_dvd (R := R) (K := K) n x v)

/-- Taking the divided divisor is a homomorphism on pre-Selmer
representatives. -/
noncomputable def rootDivisorHom (n : ℕ) :
    preSelmer (R := R) (K := K) n →*
      Multiplicative (HeightOneSpectrum R →₀ ℤ) where
  toFun x := Multiplicative.ofAdd (rootDivisor (R := R) (K := K) n x)
  map_one' := congrArg Multiplicative.ofAdd
    (rootDivisor_one (R := R) (K := K) n)
  map_mul' x y := congrArg Multiplicative.ofAdd
    (rootDivisor_mul (R := R) (K := K) n x y)

/-- The fractional ideal whose divisor is the coefficientwise divided
principal divisor. -/
noncomputable def rootIdealHom (n : ℕ) :
    preSelmer (R := R) (K := K) n →*
      (FractionalIdeal R⁰ K)ˣ :=
  (fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm.toMonoidHom.comp
    (rootDivisorHom (R := R) (K := K) n)

/-- Multiplying the divided divisor by `n` recovers the original principal
divisor. -/
theorem nsmul_rootDivisor (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    n • rootDivisor (R := R) (K := K) n x =
      Multiplicative.toAdd
        (principalDivisor (R := R) (K := K) (x : Kˣ)) := by
  ext v
  have hdvd := principalDivisor_coeff_dvd
    (R := R) (K := K) n x v
  simpa only [Finsupp.smul_apply, rootDivisor_apply, nsmul_eq_mul,
    Nat.cast_ofNat, mul_comm] using Int.ediv_mul_cancel hdvd

/-- The `n`-th power of the selected root ideal is the principal ideal of
the representative. -/
theorem rootIdealHom_pow (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    rootIdealHom (R := R) (K := K) n x ^ n =
      toPrincipalIdeal R K (x : Kˣ) := by
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  rw [map_pow]
  change (fractionalIdealDivisorMulEquiv (R := R) (K := K)
      ((fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm
        ((rootDivisorHom (R := R) (K := K) n) x))) ^ n = _
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (n • rootDivisor (R := R) (K := K) n x) =
    principalDivisor (R := R) (K := K) (x : Kˣ)
  rw [nsmul_rootDivisor]
  rfl

/-- On an actual `n`-th power, the selected root ideal is the expected
principal ideal. -/
theorem rootIdealHom_of_pow (n : ℕ) [NeZero n]
    (y : Kˣ)
    (hy : y ^ n ∈ preSelmer (R := R) (K := K) n) :
    rootIdealHom (R := R) (K := K) n ⟨y ^ n, hy⟩ =
      toPrincipalIdeal R K y := by
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  change fractionalIdealDivisorMulEquiv (R := R) (K := K)
      ((fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm
        ((rootDivisorHom (R := R) (K := K) n) ⟨y ^ n, hy⟩)) = _
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (rootDivisor (R := R) (K := K) n ⟨y ^ n, hy⟩) =
    principalDivisor (R := R) (K := K) y
  apply Multiplicative.ofAdd.injective
  ext v
  change rootDivisor (R := R) (K := K) n ⟨y ^ n, hy⟩ v =
    Multiplicative.toAdd
      (principalDivisor (R := R) (K := K) y) v
  simp only [rootDivisor_apply, map_pow,
    toAdd_pow, Finsupp.smul_apply, nsmul_eq_mul]
  exact Int.mul_ediv_cancel_left _ (Int.ofNat_ne_zero.mpr (NeZero.ne n))

/-- The class of a principal fractional ideal is trivial. -/
@[simp]
theorem classGroup_mk_toPrincipalIdeal (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 := by
  rw [ClassGroup.mk_eq_one_iff]
  exact ⟨x, by
    change ((toPrincipalIdeal R K x : FractionalIdeal R⁰ K) :
      Submodule R K) = R ∙ (x : K)
    rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]⟩

/-- Map a pre-Selmer representative to the class of its divided root
ideal. -/
noncomputable def preSelmerClassHom (n : ℕ) :
    preSelmer (R := R) (K := K) n →* ClassGroup R :=
  (ClassGroup.mk K).comp (rootIdealHom (R := R) (K := K) n)



/-- Actual `n`-th powers are pre-Selmer representatives. -/
theorem powRange_le_preSelmer (n : ℕ) :
    (powMonoidHom n : Kˣ →* Kˣ).range ≤
      preSelmer (R := R) (K := K) n := by
  rintro z ⟨y, rfl⟩
  have hq : QuotientGroup.mk
      (s := (powMonoidHom n : Kˣ →* Kˣ).range) (y ^ n) = 1 := by
    apply (QuotientGroup.eq_one_iff (y ^ n)).mpr
    exact ⟨y, rfl⟩
  change QuotientGroup.mk (y ^ n) ∈
    selmerGroup (R := R) (K := K)
      (S := (∅ : Set (HeightOneSpectrum R))) (n := n)
  rw [hq]
  exact Subgroup.one_mem _

/-- The subgroup of actual `n`-th powers inside the pre-Selmer group. -/
def preSelmerPowers (n : ℕ) :
    Subgroup (preSelmer (R := R) (K := K) n) :=
  ((powMonoidHom n : Kˣ →* Kˣ).range).subgroupOf
    (preSelmer (R := R) (K := K) n)

/-- Changing a pre-Selmer representative by an actual `n`-th power does
not change the resulting ideal class. -/
theorem preSelmerPowers_le_ker (n : ℕ) [NeZero n] :
    preSelmerPowers (R := R) (K := K) n ≤
      (preSelmerClassHom (R := R) (K := K) n).ker := by
  intro z hz
  rcases hz with ⟨y, hy⟩
  have hyPre : y ^ n ∈ preSelmer (R := R) (K := K) n :=
    powRange_le_preSelmer (R := R) (K := K) n ⟨y, rfl⟩
  have hz_eq : z = (⟨y ^ n, hyPre⟩ :
      preSelmer (R := R) (K := K) n) := by
    apply Subtype.ext
    exact hy.symm
  change preSelmerClassHom (R := R) (K := K) n z = 1
  rw [hz_eq]
  change ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n ⟨y ^ n, hyPre⟩) = 1
  rw [rootIdealHom_of_pow, classGroup_mk_toPrincipalIdeal]

/-- Send a pre-Selmer representative to its class in the empty-support
Selmer group. -/
def preSelmerToSelmer (n : ℕ) :
    preSelmer (R := R) (K := K) n →*
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) where
  toFun x := ⟨QuotientGroup.mk (x : Kˣ), x.property⟩
  map_one' := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

theorem preSelmerToSelmer_surjective (n : ℕ) :
    Function.Surjective (preSelmerToSelmer
      (R := R) (K := K) n) := by
  intro q
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective
    (powMonoidHom n : Kˣ →* Kˣ).range (q :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)
  have hxPre : x ∈ preSelmer (R := R) (K := K) n := by
    change (QuotientGroup.mk'
      (powMonoidHom n : Kˣ →* Kˣ).range) x ∈
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n)
    exact hx ▸ q.property
  refine ⟨⟨x, hxPre⟩, ?_⟩
  apply Subtype.ext
  exact hx

theorem preSelmerToSelmer_ker (n : ℕ) :
    (preSelmerToSelmer (R := R) (K := K) n).ker =
      preSelmerPowers (R := R) (K := K) n := by
  ext x
  constructor
  · intro hx
    have hq : QuotientGroup.mk (x : Kˣ) = 1 :=
      congrArg Subtype.val hx
    exact (QuotientGroup.eq_one_iff (x : Kˣ)).mp hq
  · intro hx
    apply Subtype.ext
    exact (QuotientGroup.eq_one_iff (x : Kˣ)).mpr hx

/-- The quotient of pre-Selmer representatives by actual powers is the
empty-support Selmer group. -/
noncomputable def preSelmerQuotientEquiv (n : ℕ) :
    preSelmer (R := R) (K := K) n ⧸
        preSelmerPowers (R := R) (K := K) n ≃*
      selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) :=
  QuotientGroup.liftEquiv
    (preSelmerPowers (R := R) (K := K) n)
    (preSelmerToSelmer_surjective (R := R) (K := K) n)
    (preSelmerToSelmer_ker (R := R) (K := K) n).symm

/-- Descend the root-ideal class homomorphism across actual `n`-th
powers. -/
noncomputable def quotientClassGroupHom (n : ℕ) [NeZero n] :
    preSelmer (R := R) (K := K) n ⧸
        preSelmerPowers (R := R) (K := K) n →* ClassGroup R :=
  QuotientGroup.lift
    (preSelmerPowers (R := R) (K := K) n)
    (preSelmerClassHom (R := R) (K := K) n)
    (preSelmerPowers_le_ker (R := R) (K := K) n)

/-- The canonical homomorphism from the empty-support `n`-Selmer group to
the ideal class group. -/
noncomputable def toClassGroup (n : ℕ) [NeZero n] :
    selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n) →*
      ClassGroup R :=
  (quotientClassGroupHom (R := R) (K := K) n).comp
    (preSelmerQuotientEquiv (R := R) (K := K) n).symm.toMonoidHom

/-- Formula for the class-group map on a chosen field representative. -/
theorem toClassGroup_preSelmerToSelmer (n : ℕ) [NeZero n]
    (x : preSelmer (R := R) (K := K) n) :
    toClassGroup (R := R) (K := K) n
        (preSelmerToSelmer (R := R) (K := K) n x) =
      preSelmerClassHom (R := R) (K := K) n x := by
  let e := preSelmerQuotientEquiv (R := R) (K := K) n
  have he : e (QuotientGroup.mk x) =
      preSelmerToSelmer (R := R) (K := K) n x := by
    rfl
  change quotientClassGroupHom (R := R) (K := K) n
      (e.symm (preSelmerToSelmer (R := R) (K := K) n x)) = _
  rw [← he, e.symm_apply_apply]
  rfl







/-- An integral unit, regarded as a pre-Selmer representative. -/
noncomputable def unitPreSelmer (n : ℕ) (u : Rˣ) :
    preSelmer (R := R) (K := K) n :=
  ⟨Units.map (algebraMap R K : R →+* K) u,
    (@fromUnit R _ _ K _ _ _ n u).property⟩

@[simp]
theorem preSelmerToSelmer_unitPreSelmer (n : ℕ) (u : Rˣ) :
    preSelmerToSelmer (R := R) (K := K) n
      (unitPreSelmer (R := R) (K := K) n u) =
    @fromUnit R _ _ K _ _ _ n u := by
  rfl

@[simp]
theorem rootDivisor_unitPreSelmer (n : ℕ) (u : Rˣ) :
    rootDivisor (R := R) (K := K) n
      (unitPreSelmer (R := R) (K := K) n u) = 0 := by
  ext v
  rw [rootDivisor_apply, principalDivisor_apply]
  rw [show ((unitPreSelmer (R := R) (K := K) n u :
      preSelmer (R := R) (K := K) n) : Kˣ) =
      Units.map (algebraMap R K : R →+* K) u from rfl]
  rw [HeightOneSpectrum.valuation_of_unit_eq]
  simp

@[simp]
theorem rootIdealHom_unitPreSelmer (n : ℕ) (u : Rˣ) :
    rootIdealHom (R := R) (K := K) n
      (unitPreSelmer (R := R) (K := K) n u) = 1 := by
  apply (fractionalIdealDivisorMulEquiv
    (R := R) (K := K)).injective
  change fractionalIdealDivisorMulEquiv (R := R) (K := K)
      ((fractionalIdealDivisorMulEquiv (R := R) (K := K)).symm
        ((rootDivisorHom (R := R) (K := K) n)
          (unitPreSelmer (R := R) (K := K) n u))) = _
  rw [MulEquiv.apply_symm_apply]
  change Multiplicative.ofAdd
      (rootDivisor (R := R) (K := K) n
        (unitPreSelmer (R := R) (K := K) n u)) = _
  rw [rootDivisor_unitPreSelmer, map_one]
  rfl

/-- Integral units lie in the kernel of the class-group map. -/
@[simp]
theorem toClassGroup_fromUnit (n : ℕ) [NeZero n] (u : Rˣ) :
    toClassGroup (R := R) (K := K) n
      (@fromUnit R _ _ K _ _ _ n u) = 1 := by
  rw [← preSelmerToSelmer_unitPreSelmer,
    toClassGroup_preSelmerToSelmer]
  change ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n
        (unitPreSelmer (R := R) (K := K) n u)) = 1
  rw [rootIdealHom_unitPreSelmer, map_one]

@[simp]
theorem fromUnitLift_mk (n : ℕ) [Fact (0 < n)] (u : Rˣ) :
    @fromUnitLift R _ _ K _ _ _ n _
        (QuotientGroup.mk u) =
      @fromUnit R _ _ K _ _ _ n u := by
  unfold fromUnitLift
  rw [MonoidHom.comp_apply]
  change QuotientGroup.kerLift (@fromUnit R _ _ K _ _ _ n)
      ((QuotientGroup.quotientMulEquivOfEq
        (fromUnit_ker (R := R) (K := K))).symm
          (QuotientGroup.mk u)) = _
  rw [show (QuotientGroup.quotientMulEquivOfEq
      (fromUnit_ker (R := R) (K := K))).symm
        (QuotientGroup.mk u) = QuotientGroup.mk u from rfl,
    QuotientGroup.kerLift_mk]

/-- The image of integral units modulo powers lies in the kernel. -/
theorem fromUnitLift_range_le_ker (n : ℕ) [Fact (0 < n)] [NeZero n] :
    (@fromUnitLift R _ _ K _ _ _ n _).range ≤
      (toClassGroup (R := R) (K := K) n).ker := by
  rintro q ⟨a, rfl⟩
  induction a using QuotientGroup.induction_on with
  | _ u =>
      rw [fromUnitLift_mk]
      exact MonoidHom.mem_ker.mpr
        (toClassGroup_fromUnit (R := R) (K := K) n u)

/-- If the root-ideal class of a pre-Selmer representative is trivial,
then its Selmer class comes from an integral unit. -/
theorem preSelmerToSelmer_mem_fromUnitLift_range_of_class_eq_one
    (n : ℕ) [Fact (0 < n)] [NeZero n]
    (x : preSelmer (R := R) (K := K) n)
    (hx : preSelmerClassHom (R := R) (K := K) n x = 1) :
    preSelmerToSelmer (R := R) (K := K) n x ∈
      (@fromUnitLift R _ _ K _ _ _ n _).range := by
  have hclass : ClassGroup.mk K
      (rootIdealHom (R := R) (K := K) n x) = 1 := hx
  have hprincipal := (ClassGroup.mk_eq_one_iff).mp hclass
  obtain ⟨a, haIdeal⟩ :=
    (FractionalIdeal.isPrincipal_iff
      (rootIdealHom (R := R) (K := K) n x :
        FractionalIdeal R⁰ K)).mp hprincipal
  have ha : a ≠ 0 := by
    intro ha
    subst a
    rw [FractionalIdeal.spanSingleton_zero] at haIdeal
    exact Units.ne_zero _ haIdeal
  let y : Kˣ := Units.mk0 a ha
  have hroot : rootIdealHom (R := R) (K := K) n x =
      toPrincipalIdeal R K y := by
    apply Units.ext
    rw [coe_toPrincipalIdeal]
    exact haIdeal
  have hpow := rootIdealHom_pow (R := R) (K := K) n x
  rw [hroot, ← map_pow] at hpow
  have hspan : FractionalIdeal.spanSingleton R⁰ ((y : K) ^ n) =
      FractionalIdeal.spanSingleton R⁰ ((x : Kˣ) : K) := by
    simpa only [coe_toPrincipalIdeal, Units.val_pow_eq_pow_val] using
      congrArg Units.val hpow
  obtain ⟨u, hu⟩ :=
    FractionalIdeal.spanSingleton_eq_spanSingleton.mp hspan
  have hxy : (x : Kˣ) =
      Units.map (algebraMap R K : R →+* K) u * y ^ n := by
    apply Units.ext
    change ((x : Kˣ) : K) = algebraMap R K (u : R) * (y : K) ^ n
    simpa only [Units.smul_def, Algebra.smul_def] using hu.symm
  have hyn : QuotientGroup.mk
      (s := (powMonoidHom n : Kˣ →* Kˣ).range) (y ^ n) = 1 := by
    apply (QuotientGroup.eq_one_iff (y ^ n)).mpr
    exact ⟨y, rfl⟩
  have hsel : preSelmerToSelmer (R := R) (K := K) n x =
      @fromUnit R _ _ K _ _ _ n u := by
    apply Subtype.ext
    change QuotientGroup.mk (x : Kˣ) =
      QuotientGroup.mk
        (Units.map (algebraMap R K : R →+* K) u)
    rw [hxy, QuotientGroup.mk_mul, hyn]
    exact mul_one (QuotientGroup.mk
      (s := (powMonoidHom n : Kˣ →* Kˣ).range)
      (Units.map (algebraMap R K : R →+* K) u))
  refine ⟨QuotientGroup.mk u, ?_⟩
  rw [fromUnitLift_mk]
  exact hsel.symm

/-- Every element of the kernel comes from an integral unit modulo powers. -/
theorem ker_le_fromUnitLift_range (n : ℕ)
    [Fact (0 < n)] [NeZero n] :
    (toClassGroup (R := R) (K := K) n).ker ≤
      (@fromUnitLift R _ _ K _ _ _ n _).range := by
  intro q hq
  obtain ⟨x, rfl⟩ := preSelmerToSelmer_surjective
    (R := R) (K := K) n q
  apply preSelmerToSelmer_mem_fromUnitLift_range_of_class_eq_one
    (R := R) (K := K) n x
  change toClassGroup (R := R) (K := K) n
      (preSelmerToSelmer (R := R) (K := K) n x) = 1 at hq
  rwa [toClassGroup_preSelmerToSelmer] at hq

/-- Exactness at the empty-support Selmer group: the kernel of the canonical
map to class-group `n`-torsion is precisely the image of integral units
modulo `n`-th powers. -/
theorem fromUnitLift_range_eq_ker (n : ℕ)
    [Fact (0 < n)] [NeZero n] :
    (@fromUnitLift R _ _ K _ _ _ n _).range =
      (toClassGroup (R := R) (K := K) n).ker := by
  apply le_antisymm
  · exact fromUnitLift_range_le_ker (R := R) (K := K) n
  · exact ker_le_fromUnitLift_range (R := R) (K := K) n












































end

end IsDedekindDomain.selmerGroup

end


/- Source module: EllipticCurves.X18SelmerCardinality. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/


/-!
# Cardinality bookkeeping for the `X₁(18)` two-descent

This file supplies the finite-group bookkeeping which turns checked global
square-class data into the cardinalities used by the `X₁(18)` descent.  It
uses the valuation map already attached to a Dedekind Selmer group and the
unit--Selmer--class-group exact sequence from
`MazurTorsion.NumberTheory.SelmerClassGroup`.

There is deliberately no arithmetic oracle here.  The concrete theorem at
the end consumes three independently checkable certificates:

* the cardinality of integral-unit square classes;
* surjectivity of the supported valuation map;
* a splitting of the norm on square classes.

It then proves, rather than assumes, finiteness of every group involved and
the numerical conclusions `256` and `16`.
-/

open IsDedekindDomain

namespace EllipticCurves.X18SelmerCardinality

noncomputable section

universe u v w

variable {R : Type u} [CommRing R] [IsDedekindDomain R]
variable {K : Type v} [Field K] [Algebra R K] [IsFractionRing R K]

/-! ## Explicit unit-parity certificates -/

























/-- If the class group is trivial, the empty-support Selmer group has the
same cardinality as integral units modulo `n`-th powers.  Finiteness of the
Selmer group is obtained from the displayed unit cardinality, not assumed. -/
theorem natCard_emptySelmer_eq_unitsModPow
    (n : ℕ) [Fact (0 < n)] [NeZero n]
    [Subsingleton (ClassGroup R)] :
    Nat.card (selmerGroup (R := R) (K := K)
        (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) =
      Nat.card (Units.modPow R n) := by
  let ι := @selmerGroup.fromUnitLift R _ _ K _ _ _ n _
  have hι : Function.Bijective ι := by
    refine ⟨selmerGroup.fromUnitLift_injective (R := R) (K := K), ?_⟩
    intro q
    have hq : q ∈ (selmerGroup.toClassGroup (R := R) (K := K) n).ker := by
      exact MonoidHom.mem_ker.mpr (Subsingleton.elim _ _)
    rw [← selmerGroup.fromUnitLift_range_eq_ker
      (R := R) (K := K) n] at hq
    exact hq
  exact Nat.card_congr (Equiv.ofBijective ι hι).symm

section Support

variable (S : Set (HeightOneSpectrum R)) (n : ℕ)

abbrev EmptySelmer :=
  selmerGroup (R := R) (K := K)
    (S := (∅ : Set (HeightOneSpectrum R))) (n := n)











private lemma natCard_valuation_ker
    [Finite (EmptySelmer (R := R) (K := K) n)] :
    Nat.card (supportValuation (R := R) (K := K) S n).ker =
      Nat.card (EmptySelmer (R := R) (K := K) n) := by
  let hEmptyS : EmptySelmer (R := R) (K := K) n ≤
      SupportedSelmer (R := R) (K := K) S n :=
    selmerGroup.monotone (Set.empty_subset S)
  rw [selmerGroup.valuation_ker_eq (R := R) (K := K) (S := S) (n := n)]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEmptyS).toEquiv

private lemma finite_valuation_ker
    [Finite (EmptySelmer (R := R) (K := K) n)] :
    Finite (supportValuation (R := R) (K := K) S n).ker := by
  rw [selmerGroup.valuation_ker_eq (R := R) (K := K) (S := S) (n := n)]
  let hEmptyS : EmptySelmer (R := R) (K := K) n ≤
      SupportedSelmer (R := R) (K := K) S n :=
    selmerGroup.monotone (Set.empty_subset S)
  exact Finite.of_equiv (EmptySelmer (R := R) (K := K) n)
    (Subgroup.subgroupOfEquivOfLe hEmptyS).symm.toEquiv



/-- When all supported valuation classes occur, the support factor is
exactly `n ^ #S`. -/
theorem natCard_supportedSelmer_eq_of_valuation_surjective
    [NeZero n] [Finite S] [Finite (EmptySelmer (R := R) (K := K) n)]
    (hν : Function.Surjective
      (supportValuation (R := R) (K := K) S n)) :
    Nat.card (SupportedSelmer (R := R) (K := K) S n) =
      Nat.card (EmptySelmer (R := R) (K := K) n) * n ^ Nat.card S := by
  let ν := supportValuation (R := R) (K := K) S n
  letI : Finite ν.ker := finite_valuation_ker (R := R) (K := K) S n
  letI : Finite ν.range :=
    Finite.of_injective (fun x : ν.range ↦ (x : S → Multiplicative (ZMod n)))
      Subtype.val_injective
  letI : Finite (SupportedSelmer (R := R) (K := K) S n) :=
    ν.finite_iff_finite_ker_range.mpr ⟨inferInstance, inferInstance⟩
  have hrange : Nat.card ν.range =
      Nat.card (S → Multiplicative (ZMod n)) := by
    rw [MonoidHom.range_eq_top.mpr hν, Subgroup.card_top]
  calc
    Nat.card (SupportedSelmer (R := R) (K := K) S n)
        = Nat.card ν.ker * Nat.card ν.range := by
            rw [← Subgroup.index_ker ν, ν.ker.card_mul_index]
    _ = Nat.card (EmptySelmer (R := R) (K := K) n) *
        Nat.card (S → Multiplicative (ZMod n)) := by
      rw [natCard_valuation_ker (R := R) (K := K) S n, hrange]
    _ = Nat.card (EmptySelmer (R := R) (K := K) n) * n ^ Nat.card S := by
      rw [Nat.card_fun, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

end Support

section SplitNorm

variable {G : Type v} [Group G] {H : Type w} [Group H]





end SplitNorm

section Concrete

variable (S : Set (HeightOneSpectrum R))



end Concrete

end

end EllipticCurves.X18SelmerCardinality

end


/- Source module: MazurTorsion.GroupTheory.IndexNSmulFG. Original headers retained. -/
section
/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/



/-!
# The index of multiplication on a finitely generated abelian group

This file is a narrow port of the finitely-generated-abelian-group part of
Michael Stoll's `EllipticCurves/Mathlib/SelmerGroup.lean`, commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

It extends `AddSubgroup.index_range_nsmul`, which treats a finite free
`ℤ`-module, to a finitely generated commutative group with torsion.  The
result will let a curve-specific two-descent turn a bound on
`E(ℚ) / 2 E(ℚ)` into a bound on the Mordell--Weil rank.
-/

/-- First-isomorphism counting: the cardinality of an additive group is the
cardinality of the kernel times the cardinality of the range of a homomorphism. -/
theorem AddMonoidHom.card_ker_mul_card_range {G H : Type*}
    [AddGroup G] [AddGroup H] (φ : G →+ H) :
    Nat.card φ.ker * Nat.card φ.range = Nat.card G := by
  rw [Nat.card_congr
      (QuotientAddGroup.quotientKerEquivRange φ).toEquiv.symm,
    mul_comm]
  exact
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker).symm

/-- On a finite additive group, the index of the range of an endomorphism
equals the cardinality of its kernel. -/
theorem AddMonoidHom.index_range_eq_card_ker {G : Type*}
    [AddGroup G] [Finite G] (φ : G →+ G) :
    φ.range.index = Nat.card φ.ker := by
  have h1 : φ.range.index * Nat.card φ.range = Nat.card G :=
    φ.range.index_mul_card
  exact
    Nat.eq_of_mul_eq_mul_right Nat.card_pos
      (h1.trans φ.card_ker_mul_card_range.symm)

/-- An additive equivalence maps the kernel of multiplication by `n` onto
the corresponding kernel. -/
lemma AddEquiv.map_ker_nsmulAddMonoidHom {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] (e : M ≃+ N) (n : ℕ) :
    ((nsmulAddMonoidHom (α := M) n).ker).map e.toAddMonoidHom =
      (nsmulAddMonoidHom (α := N) n).ker := by
  ext x
  rw [AddSubgroup.mem_map_equiv]
  simp only [AddMonoidHom.mem_ker, nsmulAddMonoidHom_apply]
  rw [← map_nsmul, EmbeddingLike.map_eq_zero_iff]

/-- Multiplication by `n` on a product has the product of the two ranges as
its range. -/
lemma nsmulAddMonoidHom_range_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).range =
      ((nsmulAddMonoidHom (α := A) n).range).prod
        (nsmulAddMonoidHom (α := B) n).range := by
  ext x
  simp only [AddMonoidHom.mem_range, nsmulAddMonoidHom_apply,
    AddSubgroup.mem_prod]
  exact
    ⟨fun ⟨y, hy⟩ ↦
        ⟨⟨y.1, congrArg Prod.fst hy⟩, ⟨y.2, congrArg Prod.snd hy⟩⟩,
      fun ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ↦ ⟨(a, b), Prod.ext ha hb⟩⟩

/-- Multiplication by `n` on a product has the product of the two kernels as
its kernel. -/
lemma nsmulAddMonoidHom_ker_prod (A B : Type*)
    [AddCommGroup A] [AddCommGroup B] (n : ℕ) :
    (nsmulAddMonoidHom (α := A × B) n).ker =
      ((nsmulAddMonoidHom (α := A) n).ker).prod
        (nsmulAddMonoidHom (α := B) n).ker := by
  ext x
  simp [AddMonoidHom.mem_ker, AddSubgroup.mem_prod, Prod.ext_iff]

/-- A finite module over a characteristic-zero ring has rank zero. -/
lemma Module.rank_eq_zero_of_finite (R M : Type*) [Ring R] [CharZero R]
    [AddCommGroup M] [Module R M] [Finite M] :
    Module.rank R M = 0 :=
  rank_eq_zero_iff.mpr fun x ↦
    ⟨addOrderOf x, Nat.cast_ne_zero.mpr (addOrderOf_pos x).ne',
      by
        rw [Nat.cast_smul_eq_nsmul]
        exact addOrderOf_nsmul_eq_zero x⟩

open scoped DirectSum in
open Module in
/-- The index of `nG` in a finitely generated commutative group `G` is
`n ^ rank(G)` times the cardinality of its `n`-torsion subgroup. -/
theorem AddSubgroup.index_range_nsmul_of_fg
    (G : Type*) [AddCommGroup G] [AddGroup.FG G]
    {n : ℕ} (hn : n ≠ 0) :
    (nsmulAddMonoidHom (α := G) n).range.index =
      n ^ finrank ℤ G *
        Nat.card (nsmulAddMonoidHom (α := G) n).ker := by
  obtain ⟨r, ι, fι, p, hp, e, ⟨eqv⟩⟩ :=
    AddCommGroup.equiv_free_prod_directSum_zmod G
  have hne (i : ι) : NeZero (p i ^ e i) :=
    ⟨pow_ne_zero _ (hp i).pos.ne'⟩
  have hTfin : Finite (⨁ i, ZMod (p i ^ e i)) :=
    Finite.of_equiv _ DFinsupp.equivFunOnFintype.symm
  have hidx :
      (nsmulAddMonoidHom (α := G) n).range.index =
        (nsmulAddMonoidHom
          (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).range.index := by
    simpa [AddEquiv.map_range_nsmulAddMonoidHom]
      using
        (AddSubgroup.index_map_equiv
          (nsmulAddMonoidHom (α := G) n).range eqv).symm
  have hker :
      Nat.card (nsmulAddMonoidHom (α := G) n).ker =
        Nat.card
          (nsmulAddMonoidHom
            (α := (Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) n).ker := by
    rw [← eqv.map_ker_nsmulAddMonoidHom n]
    exact
      Nat.card_congr
        (AddSubgroup.equivMapOfInjective _
          eqv.toAddMonoidHom eqv.injective).toEquiv
  have hrk : finrank ℤ G = r := by
    have h1 :
        Module.rank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      set π :=
        LinearMap.fst ℤ (Fin r →₀ ℤ) (⨁ i, ZMod (p i ^ e i))
        with hπ
      have h0 : Module.rank ℤ (LinearMap.ker π) = 0 := by
        have e2 :
            LinearMap.ker π ≃ₗ[ℤ] ⨁ i, ZMod (p i ^ e i) :=
          { toFun := fun x ↦ x.1.2
            map_add' := fun _ _ ↦ rfl
            map_smul' := fun _ _ ↦ rfl
            invFun := fun t ↦ ⟨(0, t), rfl⟩
            left_inv := fun x ↦
              Subtype.ext (Prod.ext (x.2 : x.1.1 = 0).symm rfl)
            right_inv := fun _ ↦ rfl }
        rw [e2.rank_eq]
        exact Module.rank_eq_zero_of_finite ℤ _
      rw [← π.rank_range_add_rank_ker,
        LinearMap.range_eq_top.mpr Prod.fst_surjective, rank_top,
        rank_finsupp_self', Cardinal.mk_fin, h0, add_zero]
    have h2 :
        finrank ℤ ((Fin r →₀ ℤ) × ⨁ i, ZMod (p i ^ e i)) = r := by
      simp [Module.finrank, h1]
    rw [eqv.toIntLinearEquiv.finrank_eq]
    convert h2 using 2
  have hkerF : (nsmulAddMonoidHom (α := Fin r →₀ ℤ) n).ker = ⊥ :=
    (AddMonoidHom.ker_eq_bot_iff _).mpr
      (AddSubgroup.nsmulAddMonoidHom_injective_of_isTorsionFree hn)
  rw [hidx, hker, hrk, nsmulAddMonoidHom_range_prod,
    AddSubgroup.index_prod, AddSubgroup.index_range_nsmul,
    AddMonoidHom.index_range_eq_card_ker,
    nsmulAddMonoidHom_ker_prod,
    Nat.card_congr (AddSubgroup.prodEquiv _ _).toEquiv,
    Nat.card_prod, hkerF]
  simp

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenUnitSquareclasses. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin
-/



/-!
# Unit square classes in the degree-nine `X₁(18)` two-division field

This file computes the size of the unit square-class group from the
signature alone.  It uses Dirichlet's unit theorem and the fact that an
odd-degree number field has only the roots of unity `±1`; no choice of
explicit fundamental units is required.
-/

open NumberField NumberField.InfinitePlace

namespace MazurTorsion.XOneEighteenDescent

noncomputable section

variable (L : Type*) [Field L] [NumberField L]









/-! ## The totally real cubic coefficient field -/

private theorem unitRank_eq_two
    (hdegree : Module.finrank ℚ L = 3)
    (hreal : nrRealPlaces L = 3) :
    NumberField.Units.rank L = 2 := by
  have hsignature := card_add_two_mul_card_eq_rank L
  have hcomplex : nrComplexPlaces L = 0 := by
    rw [hdegree, hreal] at hsignature
    omega
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    hreal, hcomplex]

private theorem unitTorsionOrder_eq_two_of_degree_three
    (hdegree : Module.finrank ℚ L = 3) :
    NumberField.Units.torsionOrder L = 2 := by
  apply NumberField.Units.torsionOrder_eq_two_of_odd_finrank
  rw [hdegree]
  norm_num

private theorem natCard_ker_two_units_eq_two_of_degree_three
    (hdegree : Module.finrank ℚ L = 3) :
    Nat.card
        (nsmulAddMonoidHom (α := Additive (𝓞 L)ˣ) 2).ker = 2 := by
  have htorsion : NumberField.Units.torsionOrder L = 2 :=
    unitTorsionOrder_eq_two_of_degree_three L hdegree
  have hker :
      (nsmulAddMonoidHom (α := Additive (𝓞 L)ˣ) 2).ker =
        (NumberField.Units.torsion L).toAddSubgroup := by
    ext x
    change x.toMul ^ 2 = 1 ↔ x.toMul ∈ NumberField.Units.torsion L
    rw [← NumberField.Units.rootsOfUnity_eq_torsion]
    simp [htorsion]
  rw [hker]
  change Nat.card (NumberField.Units.torsion L) = 2
  exact htorsion

/-- A totally real cubic number field has exactly eight integral-unit
square classes. -/
theorem natCard_unitsModSq_of_degree_three_of_nrRealPlaces_eq_three
    (hdegree : Module.finrank ℚ L = 3)
    (hreal : nrRealPlaces L = 3) :
    Nat.card (Units.modPow (𝓞 L) 2) = 8 := by
  have hrank : NumberField.Units.rank L = 2 :=
    unitRank_eq_two L hdegree hreal
  letI : Group.FG (𝓞 L)ˣ :=
    Group.fg_iff_monoid_fg.mpr inferInstance
  have hindex := AddSubgroup.index_range_nsmul_of_fg
    (Additive (𝓞 L)ˣ) (by norm_num : (2 : ℕ) ≠ 0)
  rw [NumberField.Units.finrank_eq, hrank,
    natCard_ker_two_units_eq_two_of_degree_three L hdegree] at hindex
  change
    (nsmulAddMonoidHom (α := Additive (𝓞 L)ˣ) 2).range.index = 8
  norm_num at hindex ⊢
  exact hindex

end

end MazurTorsion.XOneEighteenDescent

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenCoefficientFieldArithmetic. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Arithmetic of the real cubic coefficient field for the `X₁(18)` descent

The coefficient field is generated by a root of `T³ - 3T - 1`.  Its
integral power basis has discriminant `81`.  Comparing that basis with an
integral basis gives a Minkowski bound at most `2`; since `2` is inert, the
ring of integers is principal.  The same comparison proves that the field
is totally real and hence has eight unit square classes.
-/

open Module NumberField NumberField.InfinitePlace Polynomial

namespace MazurTorsion.XOneEighteenCoefficientFieldArithmetic

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes

abbrev K := MazurTorsion.XOneEighteenRealCubicQuotient.K

/-- The real cubic coefficient field has degree three. -/
theorem finrank_K_over_rat : Module.finrank ℚ K = 3 := by
  rw [_root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank, _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim]

private def coefficientDiscriminantBasis : Basis (Fin 3) ℚ K :=
  _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.basis.reindex (finCongr _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim)

private theorem coefficientDiscriminantBasis_discriminant :
    Algebra.discr ℚ coefficientDiscriminantBasis = 81 := by
  rw [coefficientDiscriminantBasis, Basis.coe_reindex,
    Algebra.discr_reindex, coefficientPowerBasis_discriminant]

private theorem coefficientDiscriminantBasis_isIntegral (i : Fin 3) :
    IsIntegral ℤ (coefficientDiscriminantBasis i) := by
  rw [coefficientDiscriminantBasis, Basis.reindex_apply,
    _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.basis_eq_pow]
  change IsIntegral ℤ
    (MazurTorsion.XOneEighteenRealCubicQuotient.tau ^
      ((finCongr _root_.MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim).symm i : ℕ))
  exact coefficientInteger.isIntegral_coe.pow _

private def reindexedIntegralBasis : Basis (Fin 3) ℚ K :=
  (integralBasis K).reindex
    ((integralBasis K).indexEquiv coefficientDiscriminantBasis)

private theorem reindexedIntegralBasis_discriminant :
    Algebra.discr ℚ reindexedIntegralBasis =
      (NumberField.discr K : ℚ) := by
  simp only [reindexedIntegralBasis, Basis.coe_reindex,
    Algebra.discr_reindex, NumberField.coe_discr]

private theorem changeMatrix_entry_isIntegral (i j : Fin 3) :
    IsIntegral ℤ
      (reindexedIntegralBasis.toMatrix coefficientDiscriminantBasis i j) := by
  let x : NumberField.RingOfIntegers K :=
    ⟨coefficientDiscriminantBasis j,
      coefficientDiscriminantBasis_isIntegral j⟩
  let e := (integralBasis K).indexEquiv coefficientDiscriminantBasis
  have hrepr := NumberField.integralBasis_repr_apply (K := K) x (e.symm i)
  rw [Basis.toMatrix_apply]
  change IsIntegral ℤ (reindexedIntegralBasis.repr (x : K) i)
  rw [show reindexedIntegralBasis.repr (x : K) i =
      (integralBasis K).repr (x : K) (e.symm i) by
    simp only [reindexedIntegralBasis, Basis.repr_reindex_apply]
    rfl]
  rw [hrepr]
  exact isIntegral_algebraMap

private theorem coefficient_discriminant_factorization :
    ∃ z : ℤ, (81 : ℤ) = z ^ 2 * NumberField.discr K := by
  have hchange :
      Algebra.discr ℚ coefficientDiscriminantBasis =
        (reindexedIntegralBasis.toMatrix coefficientDiscriminantBasis).det ^ 2 *
          Algebra.discr ℚ reindexedIntegralBasis := by
    nth_rw 1 [← reindexedIntegralBasis.toMatrix_map_vecMul
      coefficientDiscriminantBasis]
    rw [Algebra.discr_of_matrix_vecMul]
  rw [coefficientDiscriminantBasis_discriminant,
    reindexedIntegralBasis_discriminant] at hchange
  have hdet : IsIntegral ℤ
      (reindexedIntegralBasis.toMatrix coefficientDiscriminantBasis).det :=
    IsIntegral.det changeMatrix_entry_isIntegral
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.mp hdet
  rw [← hz] at hchange
  refine ⟨z, ?_⟩
  apply Rat.intCast_inj.mp
  norm_num
  exact hchange

/-- The absolute field discriminant is at most the integral power-basis
discriminant `81`. -/
theorem field_discriminant_natAbs_le :
    (NumberField.discr K).natAbs ≤ 81 := by
  obtain ⟨z, hz⟩ := coefficient_discriminant_factorization
  have hdvd : NumberField.discr K ∣ (81 : ℤ) :=
    ⟨z ^ 2, by rw [hz]; ring⟩
  exact Int.natAbs_le_of_dvd_ne_zero hdvd (by norm_num)

/-- The coefficient field discriminant is positive. -/
theorem field_discriminant_pos : 0 < NumberField.discr K := by
  obtain ⟨z, hz⟩ := coefficient_discriminant_factorization
  have hz0 : z ≠ 0 := by
    intro hz0
    rw [hz0] at hz
    norm_num at hz
  nlinarith [sq_pos_of_ne_zero hz0]

/-- The coefficient field has no complex places. -/
theorem nrComplexPlaces_eq_zero : nrComplexPlaces K = 0 := by
  have hsign := NumberField.sign_discr K
  rw [Int.sign_eq_one_of_pos field_discriminant_pos] at hsign
  have heven : Even (nrComplexPlaces K) :=
    (neg_one_pow_eq_one_iff_even (R := ℤ) (by norm_num)).mp hsign.symm
  have hsignature := card_add_two_mul_card_eq_rank K
  rw [finrank_K_over_rat] at hsignature
  obtain ⟨n, hn⟩ := heven
  omega

/-- The coefficient field is totally real. -/
theorem nrRealPlaces_eq_three : nrRealPlaces K = 3 := by
  have hsignature := card_add_two_mul_card_eq_rank K
  rw [finrank_K_over_rat, nrComplexPlaces_eq_zero] at hsignature
  omega

/-- The classical Minkowski expression for the coefficient field. -/
def minkowskiBound : ℝ :=
  (4 / Real.pi) ^ nrComplexPlaces K *
    (Nat.factorial (Module.finrank ℚ K) /
      (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
        Real.sqrt |NumberField.discr K|)

private theorem abs_discr_cast_le :
    (((|NumberField.discr K| : ℤ) : ℝ)) ≤ 81 := by
  have hInt : |NumberField.discr K| ≤ (81 : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast field_discriminant_natAbs_le
  exact_mod_cast hInt

private theorem sqrt_abs_discr_le_nine :
    Real.sqrt (((|NumberField.discr K| : ℤ) : ℝ)) ≤ 9 := by
  rw [Real.sqrt_le_iff]
  constructor
  · norm_num
  · nlinarith [abs_discr_cast_le]

/-- The coefficient-field Minkowski bound is at most `2`. -/
theorem minkowskiBound_le_two : minkowskiBound ≤ 2 := by
  rw [minkowskiBound, nrComplexPlaces_eq_zero, finrank_K_over_rat]
  norm_num [Nat.factorial]
  rw [← Int.cast_abs]
  nlinarith [sqrt_abs_discr_le_nine]

/-- The coefficient-field ring of integers is principal. -/
theorem coefficientRingOfIntegers_isPrincipal :
    IsPrincipalIdealRing (𝓞 K) := by
  apply
    RingOfIntegers.isPrincipalIdealRing_of_isPrincipal_of_pow_le_of_mem_primesOver_of_mem_Icc
  intro p hpRange hpPrime P hP hpow
  have hfloor :
      ⌊(4 / Real.pi) ^ nrComplexPlaces K *
          (Nat.factorial (Module.finrank ℚ K) /
            (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
              Real.sqrt |NumberField.discr K|)⌋₊ ≤ 2 := by
    change ⌊minkowskiBound⌋₊ ≤ 2
    exact Nat.floor_le_of_le minkowskiBound_le_two
  have hpLe : p ≤ 2 := (Finset.mem_Icc.mp hpRange).2.trans hfloor
  have hpTwo : p = 2 := by
    have hpGe : 2 ≤ p := hpPrime.two_le
    omega
  subst p
  have hinertia : P.inertiaDeg ℤ = 3 :=
    coefficient_inertiaDeg_eq_three_at_two P hP
  rw [hinertia] at hpow
  norm_num at hpow
  omega

/-- The coefficient field has exactly eight integral-unit squareclasses. -/
theorem natCard_coefficientUnitsModSq :
    Nat.card (Units.modPow (𝓞 K) 2) = 8 :=
  MazurTorsion.XOneEighteenDescent.natCard_unitsModSq_of_degree_three_of_nrRealPlaces_eq_three
    K finrank_K_over_rat nrRealPlaces_eq_three

end

end MazurTorsion.XOneEighteenCoefficientFieldArithmetic

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenCoefficientDyadicSelmer. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The dyadic supported squareclasses of the `X₁(18)` coefficient field

The rational prime `2` is inert in the real cubic coefficient field.  Thus
there is one dyadic place, the class of `2` supplies its nonzero valuation
parity, and the supported squareclass group has cardinality
`8 * 2 = 16`.
-/

open IsDedekindDomain NumberField Ideal RingOfIntegers
  UniqueFactorizationMonoid

namespace MazurTorsion.XOneEighteenCoefficientDyadicSelmer

noncomputable section

open EllipticCurves.X18SelmerCardinality
open MazurTorsion.XOneEighteenCoefficientFieldArithmetic
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes





/-- Squareclasses in the coefficient field supported at its even places. -/
abbrev DyadicSelmerK :=
  selmerGroup (R := 𝓞 K) (K := K)
    (S := coefficientDyadicSupport) (n := 2)

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

private noncomputable def chosenPrimeTwo :
    Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K) :=
  letI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  Classical.choice inferInstance

/-- A selected height-one prime above `2`.  It is proved below that this
is the unique such prime. -/
def coefficientPrimeTwo : HeightOneSpectrum (𝓞 K) :=
  .ofPrime (Ideal.prime_of_mem_primesOver (by norm_num)
    chosenPrimeTwo.property)

@[simp] theorem coefficientPrimeTwo_asIdeal :
    coefficientPrimeTwo.asIdeal = chosenPrimeTwo := rfl

theorem coefficientPrimeTwo_mem_primesOver :
    coefficientPrimeTwo.asIdeal ∈
      Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K) := by
  simpa only [coefficientPrimeTwo_asIdeal] using chosenPrimeTwo.property

private theorem absNorm_prime_over_two
    (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) :
    P.absNorm = 8 := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  rw [← Ideal.pow_inertiaDeg 2 P,
    coefficient_inertiaDeg_eq_three_at_two P hP]
  norm_num

private theorem absNorm_span_two :
    Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) = 8 := by
  calc
    Ideal.absNorm (Ideal.span {(2 : 𝓞 K)}) =
        2 ^ Module.finrank ℤ (𝓞 K) := by
      simpa using (Ideal.absNorm_span_natCast (S := 𝓞 K) 2)
    _ = 8 := by
      rw [RingOfIntegers.rank, finrank_K_over_rat]
      norm_num

private theorem prime_over_two_dvd_span
    (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) :
    P ∣ Ideal.span {(2 : 𝓞 K)} := by
  letI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  have hmap := (Ideal.liesOver_iff_dvd_map hP.1.ne_top).mp hP.2
  simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using hmap

private theorem eq_span_two_of_mem_primesOver
    (P : Ideal (𝓞 K))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) (𝓞 K)) :
    P = Ideal.span {(2 : 𝓞 K)} := by
  obtain ⟨J, hJ⟩ := prime_over_two_dvd_span P hP
  have hnorm := congrArg Ideal.absNorm hJ
  rw [map_mul, absNorm_prime_over_two P hP, absNorm_span_two] at hnorm
  have hJnorm : J.absNorm = 1 := by omega
  have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJnorm
  rw [hJtop, mul_top] at hJ
  exact hJ.symm

/-- The selected dyadic prime is the principal ideal generated by `2`. -/
theorem coefficientPrimeTwo_span :
    coefficientPrimeTwo.asIdeal = Ideal.span {(2 : 𝓞 K)} :=
  eq_span_two_of_mem_primesOver _ coefficientPrimeTwo_mem_primesOver

private theorem mem_coefficientDyadicSupport_iff
    (v : HeightOneSpectrum (𝓞 K)) :
    v ∈ coefficientDyadicSupport ↔ (2 : 𝓞 K) ∈ v.asIdeal := by
  rw [coefficientDyadicSupport, Set.mem_setOf_eq]
  constructor
  · intro hv
    by_contra hmem
    exact hv (v.valuation_eq_one_iff_notMem.mpr hmem)
  · intro hmem heq
    exact (v.valuation_eq_one_iff_notMem.mp heq) hmem

/-- The coefficient dyadic support consists of exactly one place. -/
theorem coefficientDyadicSupport_eq_singleton :
    coefficientDyadicSupport = {coefficientPrimeTwo} := by
  ext v
  rw [mem_coefficientDyadicSupport_iff, Set.mem_singleton_iff]
  constructor
  · intro htwo
    apply HeightOneSpectrum.ext
    have hspanLe : Ideal.span {(2 : 𝓞 K)} ≤ v.asIdeal := by
      rw [Ideal.span_singleton_le_iff_mem]
      exact htwo
    have hprimeLe : coefficientPrimeTwo.asIdeal ≤ v.asIdeal := by
      simpa only [coefficientPrimeTwo_span] using hspanLe
    exact
      (coefficientPrimeTwo.isMaximal.eq_of_le v.isPrime.ne_top hprimeLe).symm
  · intro hv
    subst v
    rw [coefficientPrimeTwo_span]
    exact Ideal.subset_span (Set.mem_singleton 2)

/-- The unique dyadic place as a one-element indexing equivalence. -/
def coefficientDyadicPlaceEquiv : Fin 1 ≃ coefficientDyadicSupport where
  toFun _ := ⟨coefficientPrimeTwo, by
    rw [coefficientDyadicSupport_eq_singleton]
    exact Set.mem_singleton _⟩
  invFun _ := 0
  left_inv i := Fin.ext (by omega)
  right_inv v := by
    apply Subtype.ext
    have hvMem : (v : HeightOneSpectrum (𝓞 K)) ∈
        ({coefficientPrimeTwo} : Set (HeightOneSpectrum (𝓞 K))) := by
      rw [← coefficientDyadicSupport_eq_singleton]
      exact v.property
    have hv : (v : HeightOneSpectrum (𝓞 K)) = coefficientPrimeTwo :=
      Set.mem_singleton_iff.mp hvMem
    exact hv.symm

theorem natCard_coefficientDyadicSupport :
    Nat.card coefficientDyadicSupport = 1 := by
  calc
    Nat.card coefficientDyadicSupport = Nat.card (Fin 1) :=
      (Nat.card_congr coefficientDyadicPlaceEquiv).symm
    _ = 1 := Nat.card_fin 1

private theorem two_ne_zero : (2 : K) ≠ 0 := by norm_num

/-- The coefficient-field squareclass of the dyadic uniformizer. -/
def twoSquareclass : Units.modPow K 2 :=
  QuotientGroup.mk (Units.mk0 (2 : K) two_ne_zero)

/-- The uniformizer squareclass is supported only at the dyadic place. -/
theorem twoSquareclass_mem : twoSquareclass ∈ DyadicSelmerK := by
  intro v hv
  change v.valuationOfNeZeroMod 2
      (QuotientGroup.mk (Units.mk0 (2 : K) two_ne_zero)) = 1
  rw [HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
  have hval : v.valuation K (2 : K) = 1 := by
    by_contra hne
    exact hv hne
  have hvalUnit :
      v.valuationOfNeZero (Units.mk0 (2 : K) two_ne_zero) = 1 := by
    rw [v.valuationOfNeZero_eq_iff]
    simpa only [Units.val_mk0, WithZero.coe_one] using hval
  rw [hvalUnit]
  simp

/-- The supported uniformizer class. -/
def dyadicTwo : DyadicSelmerK := ⟨twoSquareclass, twoSquareclass_mem⟩

private theorem coefficientPrimeTwo_valuation_two :
    coefficientPrimeTwo.valuation K (2 : K) =
      WithZero.exp (-1 : ℤ) := by
  calc
    coefficientPrimeTwo.valuation K (2 : K) =
        coefficientPrimeTwo.intValuation (2 : 𝓞 K) := by
      simpa only [map_ofNat] using
        coefficientPrimeTwo.valuation_of_algebraMap (K := K) (2 : 𝓞 K)
    _ = WithZero.exp (-1 : ℤ) := by
      rw [coefficientPrimeTwo.intValuation_eq_exp_neg_multiplicity
          (by norm_num), coefficientPrimeTwo_span]
      simp

private theorem coefficientPrimeTwo_valuationOfNeZero_two :
    coefficientPrimeTwo.valuationOfNeZero
        (Units.mk0 (2 : K) two_ne_zero) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  rw [coefficientPrimeTwo.valuationOfNeZero_eq_iff]
  change coefficientPrimeTwo.valuation K (2 : K) =
    WithZero.exp (-1 : ℤ)
  exact coefficientPrimeTwo_valuation_two

private theorem eq_one_or_parityOne (z : Multiplicative (ZMod 2)) :
    z = 1 ∨ z = parityOne := by
  cases z with
  | ofAdd z =>
      fin_cases z
      · left
        apply Multiplicative.toAdd.injective
        rfl
      · right
        rfl

private theorem dyadicTwo_valuation_ne_one :
    supportValuation (R := 𝓞 K) (K := K)
      coefficientDyadicSupport 2 dyadicTwo
        ⟨coefficientPrimeTwo, by
          rw [coefficientDyadicSupport_eq_singleton]
          exact Set.mem_singleton _⟩ ≠ 1 := by
  intro hone
  have hdvd : (2 : ℤ) ∣ Multiplicative.toAdd
      (coefficientPrimeTwo.valuationOfNeZero
        (Units.mk0 (2 : K) two_ne_zero)) := by
    apply (HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
      coefficientPrimeTwo 2 (Units.mk0 (2 : K) two_ne_zero)).mp
    exact hone
  rw [coefficientPrimeTwo_valuationOfNeZero_two] at hdvd
  norm_num at hdvd

private theorem dyadicTwo_valuation_eq_parityOne :
    supportValuation (R := 𝓞 K) (K := K)
      coefficientDyadicSupport 2 dyadicTwo
        ⟨coefficientPrimeTwo, by
          rw [coefficientDyadicSupport_eq_singleton]
          exact Set.mem_singleton _⟩ = parityOne := by
  rcases eq_one_or_parityOne
      (supportValuation (R := 𝓞 K) (K := K)
        coefficientDyadicSupport 2 dyadicTwo
          ⟨coefficientPrimeTwo, by
            rw [coefficientDyadicSupport_eq_singleton]
            exact Set.mem_singleton _⟩) with h | h
  · exact False.elim (dyadicTwo_valuation_ne_one h)
  · exact h

/-- Every parity at the unique dyadic place is realized. -/
theorem coefficientSupportValuation_surjective :
    Function.Surjective
      (supportValuation (R := 𝓞 K) (K := K)
        coefficientDyadicSupport 2) := by
  intro y
  let vTwo : coefficientDyadicSupport :=
    ⟨coefficientPrimeTwo, by
      rw [coefficientDyadicSupport_eq_singleton]
      exact Set.mem_singleton _⟩
  rcases eq_one_or_parityOne (y vTwo) with hy | hy
  · refine ⟨1, ?_⟩
    funext v
    have hv : v = vTwo := by
      apply Subtype.ext
      have hvMem : (v : HeightOneSpectrum (𝓞 K)) ∈
          ({coefficientPrimeTwo} : Set (HeightOneSpectrum (𝓞 K))) := by
        rw [← coefficientDyadicSupport_eq_singleton]
        exact v.property
      have hv' : (v : HeightOneSpectrum (𝓞 K)) = coefficientPrimeTwo :=
        Set.mem_singleton_iff.mp hvMem
      simpa only [vTwo] using hv'
    subst v
    simpa only [map_one, Pi.one_apply] using hy.symm
  · refine ⟨dyadicTwo, ?_⟩
    funext v
    have hv : v = vTwo := by
      apply Subtype.ext
      have hvMem : (v : HeightOneSpectrum (𝓞 K)) ∈
          ({coefficientPrimeTwo} : Set (HeightOneSpectrum (𝓞 K))) := by
        rw [← coefficientDyadicSupport_eq_singleton]
        exact v.property
      have hv' : (v : HeightOneSpectrum (𝓞 K)) = coefficientPrimeTwo :=
        Set.mem_singleton_iff.mp hvMem
      simpa only [vTwo] using hv'
    subst v
    exact dyadicTwo_valuation_eq_parityOne.trans hy.symm

/-- The dyadically supported coefficient-field squareclass group has
exactly sixteen elements. -/
theorem natCard_dyadicSelmerK : Nat.card DyadicSelmerK = 16 := by
  letI : IsPrincipalIdealRing (𝓞 K) :=
    coefficientRingOfIntegers_isPrincipal
  letI : Subsingleton (ClassGroup (𝓞 K)) := inferInstance
  letI : Fact (0 < (2 : ℕ)) := ⟨by norm_num⟩
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  letI : Finite coefficientDyadicSupport :=
    Nat.finite_of_card_ne_zero
      (natCard_coefficientDyadicSupport.trans_ne (by norm_num))
  letI : Finite (Units.modPow (𝓞 K) 2) :=
    Nat.finite_of_card_ne_zero
      (natCard_coefficientUnitsModSq.trans_ne (by norm_num))
  have hempty :
      Nat.card
          (selmerGroup (R := 𝓞 K) (K := K)
            (S := (∅ : Set (HeightOneSpectrum (𝓞 K)))) (n := 2)) = 8 :=
    (natCard_emptySelmer_eq_unitsModPow
      (R := 𝓞 K) (K := K) 2).trans natCard_coefficientUnitsModSq
  letI : Finite
      (selmerGroup (R := 𝓞 K) (K := K)
        (S := (∅ : Set (HeightOneSpectrum (𝓞 K)))) (n := 2)) :=
    Nat.finite_of_card_ne_zero (hempty.trans_ne (by norm_num))
  rw [natCard_supportedSelmer_eq_of_valuation_surjective
    (R := 𝓞 K) (K := K) coefficientDyadicSupport 2
      coefficientSupportValuation_surjective,
    hempty, natCard_coefficientDyadicSupport]
  norm_num

end

end MazurTorsion.XOneEighteenCoefficientDyadicSelmer

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenSelmerSieve. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The final finite sieve for the `X₁(18)` two-descent

This file isolates the last group-theoretic step of the concrete descent.
Its named downstream consumer is the final `X₁(18)` rank-zero module: the
global calculation enumerates sixteen possible square classes, while the
dyadic calculation admits only the identity representative.

No Selmer, local-image, or Mordell--Weil conclusion is assumed here.
-/

namespace MazurTorsion.XOneEighteenSelmerSieve



/-! ## Cardinality from opposing injections -/

/-- If a group of cardinality `256` maps to an arbitrary group, an
injected sixteen-element subgroup of its image and sixteen injected
elements of its kernel force those kernel elements to be exhaustive.

This formulation is useful for relative norms: the codomain itself need
not be finite, and the norm need not be restricted to a supported
codomain. -/
theorem kernel_representatives_bijective_of_card_256
    {G H A : Type*} [Group G] [Group H] [Group A]
    (N : G →* H)
    (representative : Fin 16 → N.ker)
    (rangeWitness : A → N.range)
    (hG : Nat.card G = 256)
    (hA : Nat.card A = 16)
    (hRepresentative : Function.Injective representative)
    (hRangeWitness : Function.Injective rangeWitness) :
    Function.Bijective representative := by
  letI : Finite G :=
    Nat.finite_of_card_ne_zero (hG.trans_ne (by norm_num))
  letI : Finite N.ker :=
    Finite.of_injective (fun x : N.ker ↦ (x : G)) Subtype.val_injective
  letI : Finite N.range :=
    Finite.of_surjective N.rangeRestrict N.rangeRestrict_surjective
  letI : Finite A :=
    Nat.finite_of_card_ne_zero (hA.trans_ne (by norm_num))
  have hkernelRange : Nat.card N.ker * Nat.card N.range = 256 := by
    rw [← Subgroup.index_ker N, N.ker.card_mul_index, hG]
  have hkernelLower : 16 ≤ Nat.card N.ker := by
    simpa only [Nat.card_fin] using
      Nat.card_le_card_of_injective representative hRepresentative
  have hrangeLower : 16 ≤ Nat.card N.range := by
    rw [← hA]
    exact Nat.card_le_card_of_injective rangeWitness hRangeWitness
  have hscaled : 16 * Nat.card N.ker ≤ 256 := by
    calc
      16 * Nat.card N.ker ≤ Nat.card N.range * Nat.card N.ker :=
        Nat.mul_le_mul_right (Nat.card N.ker) hrangeLower
      _ = Nat.card N.ker * Nat.card N.range := Nat.mul_comm _ _
      _ = 256 := hkernelRange
  have hkernelCard : Nat.card N.ker = 16 := by omega
  exact (Nat.bijective_iff_injective_and_card representative).2
    ⟨hRepresentative, by simpa only [Nat.card_fin] using hkernelCard.symm⟩

end MazurTorsion.XOneEighteenSelmerSieve

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



/-- Restriction of squareclasses from the real cubic field to the
degree-nine compositum. -/
def relativeRestrictionSquareclasses :
    Units.modPow K 2 →* Units.modPow M 2 :=
  Units.modPow.map (algebraMap K M).toMonoidHom 2

/-- Relative norm followed by restriction is the identity on squareclasses:
the extension has odd degree three. -/
theorem relativeNorm_comp_relativeRestriction :
    relativeNormSquareclasses.comp relativeRestrictionSquareclasses =
      MonoidHom.id (Units.modPow K 2) := by
  apply MonoidHom.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H u =>
      have hunit :
          Units.map (Algebra.norm K)
              (Units.map (algebraMap K M).toMonoidHom u) = u ^ 3 := by
        apply Units.ext
        simp only [Units.coe_map, Units.val_pow_eq_pow_val]
        change Algebra.norm K (algebraMap K M (u : K)) = (u : K) ^ 3
        rw [Algebra.norm_algebraMap, finrank_M_over_K]
      change
        QuotientGroup.mk
            (Units.map (Algebra.norm K)
              (Units.map (algebraMap K M).toMonoidHom u)) =
          QuotientGroup.mk u
      rw [hunit, QuotientGroup.mk_pow]
      calc
        (QuotientGroup.mk u : Units.modPow K 2) ^ 3 =
            (QuotientGroup.mk u : Units.modPow K 2) ^ 2 *
              QuotientGroup.mk u := by rw [show 3 = 2 + 1 by norm_num, pow_succ]
        _ = 1 * QuotientGroup.mk u := by rw [Units.modPow.pow_eq_one]
        _ = QuotientGroup.mk u := one_mul _























private theorem relativeNorm_fieldSquareclass_eq_one
    (x : M) (hx : x ≠ 0) (hsq : IsSquare (Algebra.norm K x)) :
    relativeNormSquareclasses (fieldSquareclass x hx) = 1 := by
  rw [relativeNormSquareclasses, fieldSquareclass,
    Units.modPow.map_mk, Units.modPow.mk_eq_one_iff_isSquare]
  simpa only [Units.coe_map, Units.val_mk0] using hsq

/-- Every explicit generator lies in the relative norm kernel. -/
theorem kernelGenerator_mem (i : Fin 4) :
    kernelGenerator i ∈ relativeNormSquareclasses.ker := by
  rw [MonoidHom.mem_ker]
  fin_cases i
  · exact relativeNorm_fieldSquareclass_eq_one h1 h1_ne_zero
      ⟨1, by simpa using norm_h1⟩
  · exact relativeNorm_fieldSquareclass_eq_one h2 h2_ne_zero
      ⟨1, by simpa using norm_h2⟩
  · exact relativeNorm_fieldSquareclass_eq_one h3 h3_ne_zero
      ⟨2, by rw [norm_h3]; norm_num⟩
  · exact relativeNorm_fieldSquareclass_eq_one h4 h4_ne_zero
      ⟨2 * (Q.tau ^ 2 - 2), by rw [norm_h4_eq_square, pow_two]⟩



/-- Every masked product remains in the relative norm kernel. -/
theorem kernelRepresentative_mem (mask : Fin 16) :
    kernelRepresentative mask ∈ relativeNormSquareclasses.ker := by
  simp only [MonoidHom.mem_ker, kernelRepresentative, map_mul]
  have hgen (i : Fin 4) : relativeNormSquareclasses (kernelGenerator i) = 1 :=
    MonoidHom.mem_ker.mp (kernelGenerator_mem i)
  split_ifs <;> simp [hgen]



/-! ## Cardinality from genuine arithmetic certificates -/







/-! ## The actual ambient relative norm -/



private theorem relativeRestriction_field_comp :
    (algebraMap RelativeIntegers M).comp
        (algebraMap (𝓞 K) RelativeIntegers) =
      (algebraMap K M).comp (algebraMap (𝓞 K) K) := by
  ext x
  rfl

/-- Scalar extension of a dyadically supported coefficient-field class
is supported at the primes above the dyadic places. -/
theorem relativeRestriction_mem_dyadicSelmer
    (x : DyadicSelmerK) :
    relativeRestrictionSquareclasses x ∈ DyadicSelmerM := by
  obtain ⟨x, hx⟩ := x
  induction x using QuotientGroup.induction_on with
  | H u =>
      intro w hw
      rw [relativeRestrictionSquareclasses, Units.modPow.map_mk,
        HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
      have hv : w.below (𝓞 K) ∉ coefficientDyadicSupport := by
        intro hv
        apply hw
        exact (HeightOneSpectrum.mem_primesAbove_iff
          (𝓞 K) RelativeIntegers coefficientDyadicSupport w).mpr hv
      exact HeightOneSpectrum.dvd_toAdd_valuationOfNeZero_map
        (algebraMap K M) (algebraMap (𝓞 K) RelativeIntegers)
        relativeRestriction_field_comp w
        (Ideal.IsIntegral.comap_ne_bot (𝓞 K) w.ne_bot) u
        ((HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
          (w.below (𝓞 K)) 2 u).mp (hx _ hv))

/-- Scalar extension restricted to the two dyadic supported groups. -/
def dyadicRelativeRestriction :
    DyadicSelmerK →* DyadicSelmerM :=
  (relativeRestrictionSquareclasses.comp DyadicSelmerK.subtype).codRestrict
    DyadicSelmerM relativeRestriction_mem_dyadicSelmer

/-- Ambient relative norm after supported scalar extension is the
underlying coefficient-field squareclass. -/
theorem fullDyadicRelativeNorm_comp_restriction :
    fullDyadicRelativeNorm.comp dyadicRelativeRestriction =
      DyadicSelmerK.subtype := by
  apply MonoidHom.ext
  intro x
  exact DFunLike.congr_fun relativeNorm_comp_relativeRestriction
    (x : Units.modPow K 2)

/-- The supported coefficient-field group injects into the range of the
ambient relative norm. -/
def dyadicBaseIntoFullNormRange
    (x : DyadicSelmerK) : fullDyadicRelativeNorm.range :=
  ⟨fullDyadicRelativeNorm (dyadicRelativeRestriction x),
    ⟨dyadicRelativeRestriction x, rfl⟩⟩

theorem dyadicBaseIntoFullNormRange_injective :
    Function.Injective dyadicBaseIntoFullNormRange := by
  intro x y hxy
  apply Subtype.ext
  have h := congrArg Subtype.val hxy
  change fullDyadicRelativeNorm (dyadicRelativeRestriction x) =
    fullDyadicRelativeNorm (dyadicRelativeRestriction y) at h
  have hx := DFunLike.congr_fun
    fullDyadicRelativeNorm_comp_restriction x
  have hy := DFunLike.congr_fun
    fullDyadicRelativeNorm_comp_restriction y
  exact hx.symm.trans (h.trans hy)



/-- Membership of the four explicit norm-kernel generators in the dyadic
Selmer group.  This is the global support certificate consumed by the
masked-product enumeration. -/
structure KernelGeneratorSupportCertificate where
  generator_mem : ∀ i : Fin 4, kernelGenerator i ∈ DyadicSelmerM

/-- Every masked product is dyadically supported once the four generators
are. -/
theorem kernelRepresentative_mem_dyadicSelmer
    (C : KernelGeneratorSupportCertificate) (mask : Fin 16) :
    kernelRepresentative mask ∈ DyadicSelmerM := by
  simp only [kernelRepresentative]
  refine mul_mem (mul_mem (mul_mem ?_ ?_) ?_) ?_ <;>
    split <;> simp [C.generator_mem]

/-- The sixteen explicit products as elements of the supported relative
norm kernel. -/
def dyadicKernelRepresentative
    (C : KernelGeneratorSupportCertificate) (mask : Fin 16) :
    fullDyadicRelativeNorm.ker := by
  refine ⟨⟨kernelRepresentative mask,
    kernelRepresentative_mem_dyadicSelmer C mask⟩, ?_⟩
  change relativeNormSquareclasses (kernelRepresentative mask) =
    (1 : Units.modPow K 2)
  exact MonoidHom.mem_ker.mp (kernelRepresentative_mem mask)

/-- Opposing injections of sixteen explicit classes into the kernel and
of the coefficient dyadic group into the range exhaust the ambient norm
kernel. -/
theorem dyadicKernelRepresentative_bijective
    (hprincipal : IsPrincipalIdealRing (𝓞 M))
    (V : DyadicValuationCertificate)
    (C : KernelGeneratorSupportCertificate)
    (hinjective : Function.Injective kernelRepresentative) :
    Function.Bijective (dyadicKernelRepresentative C) := by
  apply kernel_representatives_bijective_of_card_256
    fullDyadicRelativeNorm (dyadicKernelRepresentative C)
      dyadicBaseIntoFullNormRange
      (natCard_dyadicSelmerM hprincipal V) natCard_dyadicSelmerK
  · intro a b hab
    apply hinjective
    exact congrArg (fun z : fullDyadicRelativeNorm.ker ↦
      ((z : DyadicSelmerM) : Units.modPow M 2)) hab
  · exact dyadicBaseIntoFullNormRange_injective

/-! ## The global subgroup consumed by the Selmer sieve -/





/-! ## The unique generic descent factor -/











/-! ## Integral-closure transport for the unique factor -/































end

end MazurTorsion.XOneEighteenGlobalSelmerBridge

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenKernelGeneratorSupport. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# Dyadic support of the four `X₁(18)` norm-kernel generators

The four explicit field elements used in the global two-descent are units
away from `2`.  This file verifies that statement by integral Bézout
certificates in the normalized degree-nine order.  The first two elements
have integral inverses; the last two have an integral complementary factor
whose product with the element is exactly `2`.
-/

open IsDedekindDomain NumberField Polynomial

namespace MazurTorsion.XOneEighteenKernelGeneratorSupport

noncomputable section

open MazurTorsion.XOneEighteenCoefficientDyadicSelmer
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionSmallDiscriminant

abbrev K := MazurTorsion.XOneEighteenGlobalSelmerBridge.K

/-! ## Integral Bézout certificates -/

private def h1InversePolynomialInt : Polynomial ℤ :=
  X ^ 8 - 4 * X ^ 7 + 4 * X ^ 6 + 3 * X ^ 5 -
    6 * X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 + X

private def h1BezoutPolynomialInt : Polynomial ℤ :=
  X ^ 7 - 4 * X ^ 6 + 4 * X ^ 5 + 4 * X ^ 4 -
    10 * X ^ 3 + 3 * X ^ 2 + 3 * X - 1

private theorem h1_bezout_identity :
    h1PolynomialInt * h1InversePolynomialInt +
        h1BezoutPolynomialInt * normalizedPolynomialInt = 1 := by
  simp only [h1PolynomialInt, h1InversePolynomialInt,
    h1BezoutPolynomialInt, normalizedPolynomialInt]
  ring

private def h2InversePolynomialInt : Polynomial ℤ :=
  X ^ 7 - 4 * X ^ 6 + 4 * X ^ 5 + 3 * X ^ 4 -
    6 * X ^ 3 - 2 * X ^ 2 + 4 * X + 1

private def h2BezoutPolynomialInt : Polynomial ℤ :=
  X ^ 4 - 4 * X ^ 3 + 5 * X ^ 2 - X - 2

private theorem h2_bezout_identity :
    h2PolynomialInt * h2InversePolynomialInt +
        h2BezoutPolynomialInt * normalizedPolynomialInt = 1 := by
  simp only [h2PolynomialInt, h2InversePolynomialInt,
    h2BezoutPolynomialInt, normalizedPolynomialInt]
  ring

private def h3InversePolynomialInt : Polynomial ℤ :=
  6 * X ^ 8 - 22 * X ^ 7 + 14 * X ^ 6 + 35 * X ^ 5 -
    43 * X ^ 4 - 27 * X ^ 3 + 38 * X ^ 2 + 11 * X - 8

private def h3BezoutPolynomialInt : Polynomial ℤ :=
  6 * X ^ 7 - 28 * X ^ 6 + 42 * X ^ 5 - X ^ 4 -
    64 * X ^ 3 + 45 * X ^ 2 + 20 * X - 34

private theorem h3_bezout_identity :
    h3PolynomialInt * h3InversePolynomialInt +
        h3BezoutPolynomialInt * normalizedPolynomialInt = 2 := by
  simp only [h3PolynomialInt, h3InversePolynomialInt,
    h3BezoutPolynomialInt, normalizedPolynomialInt]
  ring

private def h4InversePolynomialInt : Polynomial ℤ :=
  7 * X ^ 8 - 25 * X ^ 7 + 14 * X ^ 6 + 42 * X ^ 5 -
    46 * X ^ 4 - 37 * X ^ 3 + 44 * X ^ 2 + 16 * X - 10

private def h4BezoutPolynomialInt : Polynomial ℤ :=
  7 * X ^ 5 - 25 * X ^ 4 + 21 * X ^ 3 + 10 * X ^ 2 -
    14 * X - 12

private theorem h4_bezout_identity :
    h4PolynomialInt * h4InversePolynomialInt +
        h4BezoutPolynomialInt * normalizedPolynomialInt = 2 := by
  simp only [h4PolynomialInt, h4InversePolynomialInt,
    h4BezoutPolynomialInt, normalizedPolynomialInt]
  ring

/-! ## Evaluation in the relative integral closure -/

private def normalizedAbsoluteInteger : 𝓞 M :=
  ⟨normalizedElement, normalizedElement_isIntegral_int⟩

private def normalizedRelativeInteger : RelativeIntegers :=
  relativeIntegersEquiv.symm normalizedAbsoluteInteger

private theorem normalizedRelativeInteger_algebraMap :
    algebraMap RelativeIntegers M normalizedRelativeInteger =
      normalizedElement := by
  rw [← IsIntegralClosure.algebraMap_equiv
    (𝓞 K) RelativeIntegers M (𝓞 M) normalizedRelativeInteger]
  change algebraMap (𝓞 M) M
      (relativeIntegersEquiv normalizedRelativeInteger) = normalizedElement
  rw [normalizedRelativeInteger,
    relativeIntegersEquiv.apply_symm_apply]
  rfl

private theorem normalizedRelativeInteger_aeval :
    Polynomial.aeval normalizedRelativeInteger normalizedPolynomialInt = 0 := by
  apply IsIntegralClosure.algebraMap_injective RelativeIntegers (𝓞 K) M
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger
        normalizedPolynomialInt) = 0
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger normalizedPolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap, map_zero] using
      normalizedPolynomialInt_aeval

private def h1RelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h1PolynomialInt

private def h2RelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h2PolynomialInt

private def h3RelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h3PolynomialInt

private def h4RelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h4PolynomialInt

private def h1InverseRelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h1InversePolynomialInt

private def h2InverseRelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h2InversePolynomialInt

private def h3InverseRelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h3InversePolynomialInt

private def h4InverseRelativeInteger : RelativeIntegers :=
  Polynomial.aeval normalizedRelativeInteger h4InversePolynomialInt

private theorem h1RelativeInteger_algebraMap :
    algebraMap RelativeIntegers M h1RelativeInteger = h1 := by
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger h1PolynomialInt) = h1
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger h1PolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap] using h1_formula.symm

private theorem h2RelativeInteger_algebraMap :
    algebraMap RelativeIntegers M h2RelativeInteger = h2 := by
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger h2PolynomialInt) = h2
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger h2PolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap] using h2_formula.symm

private theorem h3RelativeInteger_algebraMap :
    algebraMap RelativeIntegers M h3RelativeInteger = h3 := by
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger h3PolynomialInt) = h3
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger h3PolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap] using h3_formula.symm

private theorem h4RelativeInteger_algebraMap :
    algebraMap RelativeIntegers M h4RelativeInteger = h4 := by
  change (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      (Polynomial.aeval normalizedRelativeInteger h4PolynomialInt) = h4
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ RelativeIntegers M)
      normalizedRelativeInteger h4PolynomialInt]
  simpa only [IsScalarTower.toAlgHom_apply,
    normalizedRelativeInteger_algebraMap] using h4_formula.symm

private theorem h1RelativeInteger_mul_inverse :
    h1RelativeInteger * h1InverseRelativeInteger = 1 := by
  have h := congrArg (Polynomial.aeval normalizedRelativeInteger)
    h1_bezout_identity
  simpa only [map_add, map_mul, map_one,
    normalizedRelativeInteger_aeval, mul_zero, add_zero,
    h1RelativeInteger, h1InverseRelativeInteger] using h

private theorem h2RelativeInteger_mul_inverse :
    h2RelativeInteger * h2InverseRelativeInteger = 1 := by
  have h := congrArg (Polynomial.aeval normalizedRelativeInteger)
    h2_bezout_identity
  simpa only [map_add, map_mul, map_one,
    normalizedRelativeInteger_aeval, mul_zero, add_zero,
    h2RelativeInteger, h2InverseRelativeInteger] using h

private theorem h3RelativeInteger_mul_inverse :
    h3RelativeInteger * h3InverseRelativeInteger = 2 := by
  have h := congrArg (Polynomial.aeval normalizedRelativeInteger)
    h3_bezout_identity
  simpa only [map_add, map_mul, map_ofNat,
    normalizedRelativeInteger_aeval, mul_zero, add_zero,
    h3RelativeInteger, h3InverseRelativeInteger] using h

private theorem h4RelativeInteger_mul_inverse :
    h4RelativeInteger * h4InverseRelativeInteger = 2 := by
  have h := congrArg (Polynomial.aeval normalizedRelativeInteger)
    h4_bezout_identity
  simpa only [map_add, map_mul, map_ofNat,
    normalizedRelativeInteger_aeval, mul_zero, add_zero,
    h4RelativeInteger, h4InverseRelativeInteger] using h

private theorem h1_mul_inverse :
    h1 * algebraMap RelativeIntegers M h1InverseRelativeInteger = 1 := by
  rw [← h1RelativeInteger_algebraMap]
  simpa only [map_mul, map_one] using
    congrArg (algebraMap RelativeIntegers M)
      h1RelativeInteger_mul_inverse

private theorem h2_mul_inverse :
    h2 * algebraMap RelativeIntegers M h2InverseRelativeInteger = 1 := by
  rw [← h2RelativeInteger_algebraMap]
  simpa only [map_mul, map_one] using
    congrArg (algebraMap RelativeIntegers M)
      h2RelativeInteger_mul_inverse

private theorem h3_mul_inverse :
    h3 * algebraMap RelativeIntegers M h3InverseRelativeInteger = 2 := by
  rw [← h3RelativeInteger_algebraMap]
  simpa only [map_mul, map_ofNat] using
    congrArg (algebraMap RelativeIntegers M)
      h3RelativeInteger_mul_inverse

private theorem h4_mul_inverse :
    h4 * algebraMap RelativeIntegers M h4InverseRelativeInteger = 2 := by
  rw [← h4RelativeInteger_algebraMap]
  simpa only [map_mul, map_ofNat] using
    congrArg (algebraMap RelativeIntegers M)
      h4RelativeInteger_mul_inverse

/-! ## Valuations away from the dyadic support -/

private theorem valuation_two_eq_one
    (w : HeightOneSpectrum RelativeIntegers)
    (hw : w ∉ compositumDyadicSupport) :
    w.valuation M (2 : M) = 1 := by
  have hv : w.below (𝓞 K) ∉ coefficientDyadicSupport := by
    intro hv
    apply hw
    exact (HeightOneSpectrum.mem_primesAbove_iff
      (𝓞 K) RelativeIntegers coefficientDyadicSupport w).mpr hv
  have hbase : (w.below (𝓞 K)).valuation K (2 : K) = 1 := by
    simpa only [coefficientDyadicSupport, Set.mem_setOf_eq,
      not_not] using hv
  have hlies := HeightOneSpectrum.valuation_liesOver M
    (w.below (𝓞 K)) w (2 : K)
  rw [hbase, one_pow] at hlies
  simpa only [map_ofNat] using hlies.symm

private theorem valuation_h1_eq_one
    (w : HeightOneSpectrum RelativeIntegers) :
    w.valuation M h1 = 1 := by
  have hrel :
      w.valuation M (algebraMap RelativeIntegers M h1RelativeInteger) = 1 := by
    apply (w.valuation M).eq_one_of_mul_eq_one
    · exact w.valuation_le_one (K := M) h1RelativeInteger
    · exact w.valuation_le_one (K := M) h1InverseRelativeInteger
    · have hprod := congrArg (algebraMap RelativeIntegers M)
        h1RelativeInteger_mul_inverse
      have hval := congrArg (w.valuation M) hprod
      simpa only [map_mul, map_one] using hval
  rw [h1RelativeInteger_algebraMap] at hrel
  exact hrel

private theorem valuation_h2_eq_one
    (w : HeightOneSpectrum RelativeIntegers) :
    w.valuation M h2 = 1 := by
  have hrel :
      w.valuation M (algebraMap RelativeIntegers M h2RelativeInteger) = 1 := by
    apply (w.valuation M).eq_one_of_mul_eq_one
    · exact w.valuation_le_one (K := M) h2RelativeInteger
    · exact w.valuation_le_one (K := M) h2InverseRelativeInteger
    · have hprod := congrArg (algebraMap RelativeIntegers M)
        h2RelativeInteger_mul_inverse
      have hval := congrArg (w.valuation M) hprod
      simpa only [map_mul, map_one] using hval
  rw [h2RelativeInteger_algebraMap] at hrel
  exact hrel

private theorem valuation_h3_eq_one
    (w : HeightOneSpectrum RelativeIntegers)
    (hw : w ∉ compositumDyadicSupport) :
    w.valuation M h3 = 1 := by
  have hrel :
      w.valuation M (algebraMap RelativeIntegers M h3RelativeInteger) = 1 := by
    apply (w.valuation M).eq_one_of_mul_eq_one
    · exact w.valuation_le_one (K := M) h3RelativeInteger
    · exact w.valuation_le_one (K := M) h3InverseRelativeInteger
    · have hprod := congrArg (algebraMap RelativeIntegers M)
        h3RelativeInteger_mul_inverse
      have hval := congrArg (w.valuation M) hprod
      exact hval.trans (valuation_two_eq_one w hw)
  rw [h3RelativeInteger_algebraMap] at hrel
  exact hrel

private theorem valuation_h4_eq_one
    (w : HeightOneSpectrum RelativeIntegers)
    (hw : w ∉ compositumDyadicSupport) :
    w.valuation M h4 = 1 := by
  have hrel :
      w.valuation M (algebraMap RelativeIntegers M h4RelativeInteger) = 1 := by
    apply (w.valuation M).eq_one_of_mul_eq_one
    · exact w.valuation_le_one (K := M) h4RelativeInteger
    · exact w.valuation_le_one (K := M) h4InverseRelativeInteger
    · have hprod := congrArg (algebraMap RelativeIntegers M)
        h4RelativeInteger_mul_inverse
      have hval := congrArg (w.valuation M) hprod
      exact hval.trans (valuation_two_eq_one w hw)
  rw [h4RelativeInteger_algebraMap] at hrel
  exact hrel

private theorem fieldSquareclass_mem_of_valuation_eq_one
    (x : M) (hx : x ≠ 0)
    (hval : ∀ w : HeightOneSpectrum RelativeIntegers,
      w ∉ compositumDyadicSupport → w.valuation M x = 1) :
    fieldSquareclass x hx ∈ DyadicSelmerM := by
  intro w hw
  rw [fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
  have hv : w.valuationOfNeZero (Units.mk0 x hx) = 1 := by
    rw [w.valuationOfNeZero_eq_iff]
    simpa only [Units.val_mk0, WithZero.coe_one] using hval w hw
  rw [hv]
  simp

private theorem support_h1_ne_zero : h1 ≠ 0 := by
  intro hz
  have h := h1_mul_inverse
  rw [hz, zero_mul] at h
  norm_num at h

private theorem support_h2_ne_zero : h2 ≠ 0 := by
  intro hz
  have h := h2_mul_inverse
  rw [hz, zero_mul] at h
  norm_num at h

private theorem support_h3_ne_zero : h3 ≠ 0 := by
  intro hz
  have h := h3_mul_inverse
  rw [hz, zero_mul] at h
  norm_num at h

private theorem support_h4_ne_zero : h4 ≠ 0 := by
  intro hz
  have h := h4_mul_inverse
  rw [hz, zero_mul] at h
  norm_num at h

/-- Every explicit relative-norm-kernel generator is supported only at
the dyadic primes. -/
theorem kernelGenerator_mem_dyadicSelmer (i : Fin 4) :
    kernelGenerator i ∈ DyadicSelmerM := by
  fin_cases i
  · simpa only [kernelGenerator] using
      fieldSquareclass_mem_of_valuation_eq_one h1 support_h1_ne_zero
        (fun w _ ↦ valuation_h1_eq_one w)
  · simpa only [kernelGenerator] using
      fieldSquareclass_mem_of_valuation_eq_one h2 support_h2_ne_zero
        (fun w _ ↦ valuation_h2_eq_one w)
  · simpa only [kernelGenerator] using
      fieldSquareclass_mem_of_valuation_eq_one h3 support_h3_ne_zero
        valuation_h3_eq_one
  · simpa only [kernelGenerator] using
      fieldSquareclass_mem_of_valuation_eq_one h4 support_h4_ne_zero
        valuation_h4_eq_one

/-- The unconditional support certificate consumed by the global Selmer
enumeration. -/
theorem kernelGeneratorSupportCertificate :
    KernelGeneratorSupportCertificate :=
  ⟨kernelGenerator_mem_dyadicSelmer⟩

end

end MazurTorsion.XOneEighteenKernelGeneratorSupport

end

/- Copyright (c) 2026 Vasily Ilin. Released under Apache-2.0.
Unconditional enumeration of the full supported relative norm kernel. -/
theorem solution
    (z : MazurTorsion.XOneEighteenGlobalSelmerBridge.fullDyadicRelativeNorm.ker) :
    ∃ mask : Fin 16,
      MazurTorsion.XOneEighteenGlobalSelmerBridge.kernelRepresentative mask =
        ((z : MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicSelmerM) :
          Units.modPow MazurTorsion.XOneEighteenTwoDivisionArithmetic.M 2) := by
  have hb := MazurTorsion.XOneEighteenGlobalSelmerBridge.dyadicKernelRepresentative_bijective
    MazurTorsion.XOneEighteenTwoDivisionClassNumberOne.compositumRingOfIntegers_isPrincipal
    MazurTorsion.XOneEighteenDyadicValuationCertificate.dyadicValuationCertificate
    MazurTorsion.XOneEighteenKernelGeneratorSupport.kernelGeneratorSupportCertificate
    MazurTorsion.XOneEighteenDyadicKernelSeparation.kernelRepresentative_injective
  obtain ⟨mask, hmask⟩ := hb.2 z
  refine ⟨mask, ?_⟩
  exact congrArg
    (fun z : MazurTorsion.XOneEighteenGlobalSelmerBridge.fullDyadicRelativeNorm.ker =>
      ((z : MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicSelmerM) :
        Units.modPow MazurTorsion.XOneEighteenTwoDivisionArithmetic.M 2)) hmask
#print axioms solution
