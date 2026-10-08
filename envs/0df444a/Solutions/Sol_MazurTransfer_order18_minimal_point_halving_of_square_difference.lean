-- Prove2me | solution 1 for MazurTransfer.order18_minimal_point_halving_of_square_difference
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T16:44:52.436505+00:00
-- url     : https://prove2.me/submissions/124d57dc-4c68-4b5a-9bf4-29d141e55d6c

import Mathlib
import Definitions.Def_MazurTransfer_Order18MinimalHalvingData
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





lemma eq_zero_of_monic_dvd_of_degree_lt (hg : g.Monic) (hdvd : g ∣ q)
    (hq : q.degree < g.degree) : q = 0 :=
  ((modByMonic_eq_self_iff hg).mpr hq).symm.trans <| (modByMonic_eq_zero_iff_dvd hg).mpr hdvd







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

@[simp]
lemma mk_modByMonic (hg : g.Monic) (q : R[X]) : mk g (q %ₘ g) = mk g q := by
  simpa using mk_leftInverse hg (mk g q)

lemma exists_degree_lt_mk_eq [Nontrivial R] (hg : g.Monic) (a : AdjoinRoot g) :
    ∃ p, p.degree < g.degree ∧ a = mk g p := by
  obtain ⟨q, rfl⟩ := mk_surjective a
  exact ⟨q %ₘ g, degree_modByMonic_lt q hg, (mk_modByMonic hg q).symm⟩

lemma mk_eq_mk_iff_of_degree_lt [Nontrivial R] (hg : g.Monic) {p q : R[X]}
    (hp : p.degree < g.degree) (hq : q.degree < g.degree) :
    mk g p = mk g q ↔ p = q :=
  ⟨fun h ↦ sub_eq_zero.mp <| eq_zero_of_monic_dvd_of_degree_lt hg (mk_eq_mk.mp h) <|
    (degree_sub_le p q).trans_lt (max_lt hp hq), fun h ↦ h ▸ rfl⟩













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

lemma ringChar_ne_two [W.IsElliptic] [W.IsCharNeTwoNF] : ringChar K ≠ 2 := by
  have h := W.isUnit_Δ.ne_zero
  contrapose! h
  have h2 : (2 : K) = 0 := by
    have := ringChar.Nat.cast_ringChar (R := K)
    rw [h] at this
    exact_mod_cast this
  rw [Δ_of_isCharNeTwoNF W]
  linear_combination (-32 * W.a₂ ^ 3 * W.a₆ + 8 * W.a₂ ^ 2 * W.a₄ ^ 2 - 32 * W.a₄ ^ 3
    - 216 * W.a₆ ^ 2 + 144 * W.a₂ * W.a₄ * W.a₆) * h2

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

lemma degree_lt_degree_f {p : K[X]} (hp : p.natDegree ≤ 2) : p.degree < W.f.degree :=
  degree_lt_degree <| by rw [natDegree_f]; lia









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

@[simp]
lemma negY_of_isCharNeTwoNF [W.IsCharNeTwoNF] (x y : K) : W.negY x y = -y := by
  rw [negY, a₁_of_isCharNeTwoNF, a₃_of_isCharNeTwoNF]
  ring



/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] :=
  X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)

lemma natDegree_fCofactor (x : K) : (W.fCofactor x).natDegree = 2 := by
  simp only [fCofactor]
  compute_degree!

lemma monic_fCofactor (x : K) : (W.fCofactor x).Monic := by
  simp only [fCofactor]
  monicity!

lemma degree_lt_degree_fCofactor (x : K) {p : K[X]} (hp : p.natDegree ≤ 1) :
    p.degree < (W.fCofactor x).degree :=
  degree_lt_degree <| by rw [natDegree_fCofactor]; lia

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
private lemma f_dvd_of_fCofactor_dvd {x r s : K} (hx : W.f.eval x = 0) (hr : r ≠ 0)
    (hdvd : W.fCofactor x ∣ (C r * X + C s) ^ 2 - (C x - X)) :
    W.f ∣ (X - C (-s / r)) ^ 2 * (X - C x) - -(C (1 / r) * X + C (-x / r)) ^ 2 := by
  obtain ⟨q, hq⟩ := hdvd
  apply_fun (· * (X - C x)) at hq
  rw [mul_right_comm, ← f_eq_mul_of_eval_eq_zero _ hx] at hq
  replace hq : q * W.f = ((C r * X + C s) ^ 2 - (C x - X)) * (X - C x) := by
    rw [mul_comm]; exact hq.symm
  refine ⟨C (1 / r ^ 2) * q, ?_⟩
  rw [eq_comm, mul_comm W.f]
  apply_fun (C (r ^ 2) * ·) using mul_right_injective₀ <| by simp [hr]
  dsimp only
  rw [← mul_assoc, ← mul_assoc, ← map_mul]
  rw [mul_one_div_cancel <| pow_ne_zero 2 hr, map_one, one_mul, hq]
  conv_rhs =>
    rw [sub_neg_eq_add, mul_add, ← mul_assoc, map_pow, ← mul_pow, mul_sub (C r), ← map_mul,
      mul_div_cancel₀ _ hr]
    enter [2]
    rw [← mul_pow, mul_add, ← mul_assoc, ← map_mul, mul_one_div_cancel hr, map_one, one_mul,
      ← map_mul, mul_div_cancel₀ _ hr]
  simp only [C_eq_algebraMap]
  algebra

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

lemma exists_mk_eq (a : W.A) :
    ∃ r s t, a = AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq W.monic_f a
  rw [degree_eq_natDegree W.monic_f.ne_zero, natDegree_f] at hp
  exact ⟨_, _, _, congrArg (AdjoinRoot.mk W.f) <|
    eq_quadratic_of_degree_le_two <| Order.lt_succ_iff.mp hp⟩

lemma exists_X_sub_C_mul_eq (r s t : K) (hr : r ≠ 0) :
    ∃ ξ l m, AdjoinRoot.mk W.f (X - C ξ) * AdjoinRoot.mk W.f (C r * X ^ 2 + C s * X + C t) =
       AdjoinRoot.mk W.f (C l * X + C m) := by
  conv => enter [1, ξ, 1, l, 1, m]; rw [← map_mul, ← sub_eq_zero, ← map_sub]
  have H (ξ l m : K) : (X - C ξ) * (C r * X ^ 2 + C s * X + C t) - (C l * X + C m) =
      C r * W.f + (C (-ξ * r + s - W.a₂ * r) * X ^ 2 + C (-ξ * s - l - W.a₄ * r + t) * X
        + C (-ξ * t - m - W.a₆ * r)) := by
    simp only [f, C_eq_algebraMap]
    algebra
  conv =>
    enter [1, ξ, 1, l, 1, m]
    rw [H, map_add, map_mul]
    enter [1, 1, 2]
    rw [AdjoinRoot.mk_self]
  simp only [mul_zero, zero_add]
  suffices ∃ ξ l m, -ξ * r + s - W.a₂ * r = 0 ∧ -ξ * s - l - W.a₄ * r + t = 0 ∧
      -ξ * t - m - W.a₆ * r = 0 by
    obtain ⟨ξ, l, m, h₂, h₁, h₀⟩ := this
    refine ⟨ξ, l, m, ?_⟩
    rw [h₂, h₁, h₀]
    simp
  refine ⟨s / r - W.a₂, t - W.a₄ * r - s ^ 2 / r + W.a₂ * s,
    -W.a₆ * r - t * s / r + W.a₂ * t, ?_, ?_, ?_⟩ <;> field

/-- The étale algebra associated to the cofactor of `f`. -/
abbrev A' (x : K) : Type _ := AdjoinRoot (W.fCofactor x)

lemma exists_mk_eq' {x : K} (a : W.A' x) :
    ∃ r s, a = AdjoinRoot.mk (W.fCofactor x) (C r * X + C s) := by
  obtain ⟨p, hp, rfl⟩ := AdjoinRoot.exists_degree_lt_mk_eq (W.monic_fCofactor x) a
  rw [degree_eq_natDegree (W.monic_fCofactor x).ne_zero, natDegree_fCofactor] at hp
  exact ⟨_, _, congrArg (AdjoinRoot.mk (W.fCofactor x)) <|
    eq_X_add_C_of_natDegree_le_one <| natDegree_le_of_degree_le <| Order.lt_succ_iff.mp hp⟩









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
private lemma exists_pol_of_eq_two_smul {x y : K} (h : W.Nonsingular x y) {P : W.Point}
    (hP : Point.some x y h = 2 • P) :
    ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  match P with
  | 0 => simp at hP -- cannot occur
  | .some ξ η h' =>
    rw [← sub_eq_zero, sub_eq_add_neg, two_smul, neg_add, ← add_assoc, add_rotate,
      Point.neg_some] at hP
    have H : W.Nonsingular ξ (W.negY ξ η) := (nonsingular_neg ξ η).mpr h'
    obtain ⟨pol, hpol, hpol₁⟩ := Point.some_add_some_add_some_eq_zero H H h hP
    rw [← sq] at hpol
    obtain ⟨l, m, rfl⟩ := exists_eq_X_add_C_of_natDegree_le_one hpol₁
    exact ⟨_, _, _, hpol⟩

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
private lemma exists_eq_two_smul_of_identities {x y ξ l m : K} (h : W.Nonsingular x y)
    (H₂ : x + 2 * ξ = l ^ 2 - W.a₂) (H₁ : 2 * x * ξ + ξ ^ 2 = W.a₄ - 2 * l * m)
    (H₀ : x * ξ ^ 2 = -W.a₆ + m ^ 2) :
    ∃ P, Point.some x y h = 2 • P := by
  have h20 : (2 : K) ≠ 0 := Ring.two_ne_zero <| ringChar_ne_two W
  have hy₀ : l * ξ + m ≠ 0 := by
    have hΔ := W.isUnit_Δ.ne_zero
    rw [Δ_of_isCharNeTwoNF W] at hΔ
    contrapose! hΔ
    -- the Bézout certificate for `Δ`, evaluated at `ξ`, where `f ξ = (lξ+m)²` and
    -- `f' ξ = 2l(lξ+m)` vanish by `hΔ` and the coefficient identities
    linear_combination
      (((288 * W.a₄ - 96 * W.a₂ ^ 2) * ξ + (240 * W.a₂ * W.a₄ - 64 * W.a₂ ^ 3 - 432 * W.a₆)) *
          ((l * ξ + m) * hΔ + ξ ^ 2 * H₂ - ξ * H₁ + H₀))
        + (((32 * W.a₂ ^ 2 - 96 * W.a₄) * ξ ^ 2
            + (32 * W.a₂ ^ 3 - 112 * W.a₂ * W.a₄ + 144 * W.a₆) * ξ
            + (16 * W.a₂ ^ 2 * W.a₄ - 64 * W.a₄ ^ 2 + 48 * W.a₂ * W.a₆)) *
          (2 * l * hΔ + 2 * ξ * H₂ - H₁))
  have hy : l * ξ + m ≠ W.negY ξ (l * ξ + m) := by
    rw [negY_of_isCharNeTwoNF]
    grind
  have hsl : W.slope ξ ξ (l * ξ + m) (l * ξ + m) = l := by
    simp only [slope_of_Y_ne rfl hy, a₁_of_isCharNeTwoNF, zero_mul, sub_zero,
      negY_of_isCharNeTwoNF, sub_neg_eq_add, ← two_mul]
    rw [mul_comm] at hy₀ -- `field_simp` changes `l * ξ` to `ξ * l`
    field_simp
    grobner
  have heq : W.Equation ξ (l * ξ + m) := by
    rw [equation_iff_eval_f_eq_sq, eval_f]
    linear_combination ξ ^ 2 * H₂ - ξ * H₁ + H₀
  let P : W.Point := .some ξ (l * ξ + m) <| equation_iff_nonsingular.mp heq
  suffices .some x y h = 2 • P ∨ .some x y h = 2 • (-P) from this.casesOn (⟨_, ·⟩) (⟨_, ·⟩)
  simp only [smul_neg, P, two_smul, Point.add_self_of_Y_ne hy, ← Point.X_eq_iff, hsl, addX,
    a₁_of_isCharNeTwoNF, zero_mul, add_zero]
  linear_combination H₂

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity of polynomials. -/
lemma exists_eq_two_smul_iff {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, (X - C ξ) ^ 2 * (X - C x) = W.f - (C l * X + C m) ^ 2 := by
  refine ⟨fun ⟨P, hP⟩ ↦ exists_pol_of_eq_two_smul h hP, fun ⟨ξ, l, m, H⟩ ↦ ?_⟩
  have H' : X ^ 3 - C (x + 2 * ξ) * X ^ 2 + C (2 * x * ξ + ξ ^ 2) * X - C (x * ξ ^ 2) =
      X ^ 3 - C (l ^ 2 - W.a₂) * X ^ 2 + C (W.a₄ - 2 * l * m) * X - C (-W.a₆ + m ^ 2) := by
    simp only [f] at H
    convert H using 1 <;> { simp only [C_eq_algebraMap]; algebra }
  replace H' n := congrArg (fun p ↦ p.coeff n) H'
  simp only [coeff_sub, coeff_add, coeff_X_pow, coeff_C_mul_X_pow, coeff_C_mul_X, coeff_C] at H'
  exact exists_eq_two_smul_of_identities h (by simpa using congrArg (-·) (H' 2))
    (by simpa using H' 1) (by simpa using congrArg (-·) (H' 0))

/-- A criterion for a nonsingular point in affine coordinates to be divisible by 2,
in terms of an identity in `W.A`. -/
lemma exists_eq_two_smul_iff' {x y : K} (h : W.Nonsingular x y) :
    (∃ P, Point.some x y h = 2 • P) ↔
      ∃ ξ l m, AdjoinRoot.mk W.f ((X - C ξ) ^ 2 * (X - C x)) =
        AdjoinRoot.mk W.f (-(C l * X + C m) ^ 2) := by
  rw [exists_eq_two_smul_iff]
  refine ⟨fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩, fun ⟨ξ, l, m, H⟩ ↦ ⟨ξ, l, m, ?_⟩⟩
  · rw [H, map_sub, sub_eq_add_neg, map_neg, add_eq_right]
    simp
  · rw [AdjoinRoot.mk_eq_mk, sub_neg_eq_add] at H
    have hmon : ((X - C ξ) ^ 2 * (X - C x) + (C l * X + C m) ^ 2).Monic := by monicity!
    have hf := eq_of_dvd_of_natDegree_le_of_leadingCoeff H
      (by rw [natDegree_f]; compute_degree!) (by rw [W.monic_f.leadingCoeff, hmon.leadingCoeff])
    linear_combination -hf

section kernel

variable {x y : K} (h : W.Nonsingular x y)

include h

private lemma eq_two_smul_of_μ_eq_one_of_ne (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x ≠ 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨r, s, t, hrst⟩ := W.exists_mk_eq z
  rw [hrst] at hz
  have hr : r ≠ 0 := by
    intro rfl
    simp only [map_zero, zero_mul, zero_add, ← map_pow] at hz
    rw [AdjoinRoot.mk_eq_mk_iff_of_degree_lt W.monic_f
      (W.degree_lt_degree_f (by compute_degree!))
      (W.degree_lt_degree_f (by compute_degree!))] at hz
    apply_fun natDegree at hz
    have hd : (C x - X).natDegree = 1 := by compute_degree!
    rw [natDegree_pow, hd] at hz
    lia
  obtain ⟨ξ, l, m, H⟩ := W.exists_X_sub_C_mul_eq r s t hr
  rw [← map_mul] at H
  refine ⟨ξ, l, m, ?_⟩
  apply_fun (fun p ↦ AdjoinRoot.mk W.f (X - C ξ) ^ 2 * p) at hz
  rw [← neg_inj, eq_comm, ← map_pow, ← map_mul, ← map_neg] at hz
  conv_rhs at hz => rw [← map_pow, ← map_mul, ← mul_pow, map_pow, H, ← map_pow, ← map_neg]
  convert hz
  ring

private lemma eq_two_smul_of_μ_eq_one_of_eq (hμ : (μ <| .ofAdd <| .some x y h) = 1)
    (hx : W.f.eval x = 0) : ∃ P : W.Point, .some x y h = 2 • P := by
  rw [exists_eq_two_smul_iff']
  rw [μ_apply, μ₀_some, μX_of_eval_f_eq_zero hx, Units.modPow.unit_eq_one_iff] at hμ
  obtain ⟨z, hz⟩ := hμ
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective z
  obtain ⟨r, s, hrs⟩ := W.exists_mk_eq' (AdjoinRoot.mk (W.fCofactor x) p)
  rw [← hp, ← map_pow, AdjoinRoot.mk_eq_mk] at hz
  have hdvd : W.fCofactor x ∣ W.f := ⟨X - C x, W.f_eq_mul_of_eval_eq_zero hx⟩
  have hz' : AdjoinRoot.mk (W.fCofactor x) (p ^ 2) =
      AdjoinRoot.mk (W.fCofactor x) (C x - X + W.fCofactor x) :=
    AdjoinRoot.mk_eq_mk.mpr <| hdvd.trans hz
  rw [map_pow, hrs, map_add _ _ (fCofactor ..), AdjoinRoot.mk_self, add_zero] at hz'
  have hr₀ : r ≠ 0 := by
    intro rfl
    rw [map_zero, zero_mul, zero_add, ← map_pow,
      AdjoinRoot.mk_eq_mk_iff_of_degree_lt (W.monic_fCofactor x)
        (W.degree_lt_degree_fCofactor x (by compute_degree!))
        (W.degree_lt_degree_fCofactor x (by compute_degree!))] at hz'
    apply_fun natDegree at hz'
    have hd : (C x - X).natDegree = 1 := by compute_degree!
    rw [natDegree_pow, hd] at hz'
    lia
  rw [← map_pow, AdjoinRoot.mk_eq_mk] at hz'
  exact ⟨-s / r, 1 / r, -x / r, AdjoinRoot.mk_eq_mk.mpr (W.f_dvd_of_fCofactor_dvd hx hr₀ hz')⟩

lemma eq_two_smul_of_μ_eq_one (hμ : (μ <| .ofAdd <| .some x y h) = 1) :
    ∃ P : W.Point, .some x y h = 2 • P := by
  rcases eq_or_ne (W.f.eval x) 0 with hx | hx
  · exact eq_two_smul_of_μ_eq_one_of_eq h hμ hx
  · exact eq_two_smul_of_μ_eq_one_of_ne h hμ hx

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

open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open WeierstrassCurve.Affine

theorem solution (x y : K)
    (h : minimalDescentCurve.toAffine.Nonsingular x y)
    (hsq : IsSquare (algebraMap K M x - minimalDescentRootInM)) :
    ∃ Q : minimalDescentCurve.toAffine.Point,
      2 • Q = .some x y h := by
  have hx : minimalDescentCurve.toAffine.f.eval x ≠ 0 := by
    exact minimalDescentPolynomial_irreducible.not_isRoot_of_natDegree_ne_one
      (by rw [minimalDescentCurve.toAffine.natDegree_f]; norm_num)
  have hmu : WeierstrassCurve.Affine.μ
      (W := minimalDescentCurve.toAffine) (.ofAdd (.some x y h)) = 1 := by
    apply minimalDescentSquareclassEquiv.injective
    rw [map_one, μ_apply, μ₀_some, μX_of_eval_f_ne_zero hx]
    change (QuotientGroup.mk
      (Units.mapEquiv minimalDescentAlgebraEquiv.toMulEquiv
        ((isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit)) : Units.modPow M 2) = 1
    apply Units.modPow.mk_eq_one_iff_isSquare.mpr
    have hv : ((Units.mapEquiv minimalDescentAlgebraEquiv.toMulEquiv
        ((isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit)) : M) =
        algebraMap K M x - minimalDescentRootInM := by
      change minimalDescentAlgebraEquiv
        (((isUnit_mk_sub_X_of_eval_f_ne_zero hx).unit) : minimalDescentCurve.toAffine.A) = _
      rw [IsUnit.unit_spec, map_sub, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_sub]
      change minimalDescentAlgebraEquiv
        (algebraMap K minimalDescentCurve.toAffine.A x) -
          minimalDescentAlgebraEquiv minimalGenericRoot = _
      rw [minimalDescentAlgebraEquiv.commutes, minimalDescentAlgebraEquiv_genericRoot]
    rw [hv]
    exact hsq
  obtain ⟨Q, hQ⟩ := WeierstrassCurve.Affine.eq_two_smul_of_μ_eq_one h hmu
  exact ⟨Q, hQ.symm⟩
#print axioms solution
