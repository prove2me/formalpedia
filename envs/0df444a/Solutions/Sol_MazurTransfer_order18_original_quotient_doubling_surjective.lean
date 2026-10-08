-- Prove2me | solution 1 for MazurTransfer.order18_original_quotient_doubling_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T17:49:02.694127+00:00
-- url     : https://prove2.me/submissions/c19060fc-1b12-4e42-938b-325e66bf445e

import Mathlib
import Theorems.Thm_MazurTransfer_order18_minimal_point_halving_of_square_difference
import Theorems.Thm_MazurTransfer_order18_affine_point_global_kernel_mask
import Theorems.Thm_MazurTransfer_order18_affine_point_local_kernel_mask_zero
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













/-- The quotient of `f` by `X - x`. -/
noncomputable abbrev fCofactor (x : K) : K[X] :=
  X ^ 2 + C (x + W.a₂) * X + C (x ^ 2 + W.a₂ * x + W.a₄)









lemma fCofactor_mul_eq (x : K) : W.fCofactor x * (X - C x) = W.f - C (W.f.eval x) := by
  simp only [fCofactor, f, eval_add, eval_pow, eval_X, eval_mul, eval_C, map_add, map_pow,
    map_mul, add_sub_add_right_eq_sub]
  algebra







/- Dividing the relation `(r X + s)² ≡ x - X mod (fCofactor x)` by `r²` yields the polynomial
identity certifying that a point with `2`-torsion `x`-coordinate `x` is divisible by `2`
(used in Step 4). -/






/-- The étale algebra associated to a Weierstrass curve with `a₁ = a₃ = 0`. -/
abbrev A : Type _ := AdjoinRoot W.f

lemma finrank_A : Module.finrank K W.A = 3 := by
  rw [(AdjoinRoot.powerBasis W.f_ne_zero).finrank, AdjoinRoot.powerBasis_dim, natDegree_f]

























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



variable [W.IsElliptic]






end

/-!
### Step 2: define `M` and `μ` as a plain map `μ₀`
-/



/- `inferInstance` succeeds here, but instance search does not find this instance at the use
sites (e.g., for `mul_right_comm` below) unless it is declared. -/








variable [DecidableEq K] [W.IsCharNeTwoNF]

section μ₀

variable [W.IsElliptic]













end μ₀

/-!
### Step 3: show that `μ` is a homomorphism `Multiplicative W.Point → M`
-/







/- Forward direction of `exists_eq_two_smul_iff`: if `(x, y)` is divisible by `2`, then the
polynomial identity holds, with `ξ` the `x`-coordinate of a halving point. -/


variable [W.IsElliptic]

section μ₀_helper_lemmas

open Point



variable {xP yP xQ yQ xR yR : K} (hP : W.Nonsingular xP yP) (hQ : W.Nonsingular xQ yQ)
  (hR : W.Nonsingular xR yR) (hPQR : some xP yP hP + some xQ yQ hQ + some xR yR hR = 0)

include hPQR



/- The case where only `xP` is a `2`-torsion `x`-coordinate. -/






end μ₀_helper_lemmas









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


/- Source module: MazurTorsion.EllipticCurve.VariableChange. Original headers retained. -/
section
/-
Copyright (c) 2026 Kevin Buzzard, Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll, Claude, Vasily Ilin
-/


/-!
# Isomorphism of point groups induced by a change of variables

This file is ported from Michael Stoll's Apache-2.0 `EllipticCurves` project at commit
`3f8c39c0fc4c0fd0a40e693aa2a9bbda08d9ee1f`.

The derivative-transport and singular-cubic nonsingular-locus equivalence are local extensions.
They generalize the ported point equivalence beyond elliptic equations while retaining the
original admissible change-of-variables formulas and attribution.

Mathlib's affine `Point` API provides the group homomorphism induced by a change of the base
field for a fixed Weierstrass curve, but not the isomorphism of Mordell--Weil groups induced by
an admissible change of variables between two different curves. For
`C : WeierstrassCurve.VariableChange F`, the admissible change

`(x, y) ↦ (u²x + r, u³y + u²sx + t)`

gives the group isomorphism
`WeierstrassCurve.Affine.Point.equivVariableChange : (C • W).Point ≃+ W.Point`.
Its inverse is the explicit change of variables `C⁻¹`.
-/

section

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] (W : WeierstrassCurve F) (C : VariableChange F)

/-! ### Transformation of the group-law formulae under a change of variables -/

lemma variableChange_negY (x y : F) :
    W.toAffine.negY ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      = (C.u : F) ^ 3 * (C • W).toAffine.negY x y + (C.u : F) ^ 2 * C.s * x + C.t := by
  simp [negY, variableChange_a₁, variableChange_a₃]
  field

/-- The image of a pair of points under the change of variables satisfies the `y₁ = -y₂`
degeneracy condition only if the original pair does. -/
lemma variableChange_negY_ne {x₁ x₂ y₁ y₂ : F}
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    ¬((C.u : F) ^ 2 * x₁ + C.r = (C.u : F) ^ 2 * x₂ + C.r ∧
      (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t = W.toAffine.negY
        ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  intro ⟨hX, hY⟩
  have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
  subst hx
  rw [variableChange_negY] at hY
  exact hxy ⟨rfl, mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY)⟩

lemma variableChange_addX (x₁ x₂ ℓ : F) :
    W.toAffine.addX ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 2 * (C • W).toAffine.addX x₁ x₂ ℓ + C.r := by
  simp [addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_negAddY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.negAddY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.negAddY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp [negAddY, addX, variableChange_a₁, variableChange_a₂]
  field

lemma variableChange_addY (x₁ x₂ y₁ ℓ : F) :
    W.toAffine.addY ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) ((C.u : F) * ℓ + C.s)
      = (C.u : F) ^ 3 * (C • W).toAffine.addY x₁ x₂ y₁ ℓ
        + (C.u : F) ^ 2 * C.s * (C • W).toAffine.addX x₁ x₂ ℓ + C.t := by
  simp only [addY, variableChange_negAddY, variableChange_addX, variableChange_negY]

lemma variableChange_slope [DecidableEq F] {x₁ x₂ y₁ y₂ : F}
    (h₁ : (C • W).toAffine.Equation x₁ y₁) (h₂ : (C • W).toAffine.Equation x₂ y₂)
    (hxy : ¬(x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂)) :
    W.toAffine.slope ((C.u : F) ^ 2 * x₁ + C.r) ((C.u : F) ^ 2 * x₂ + C.r)
        ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t)
        ((C.u : F) ^ 3 * y₂ + (C.u : F) ^ 2 * C.s * x₂ + C.t)
      = (C.u : F) * (C • W).toAffine.slope x₁ x₂ y₁ y₂ + C.s := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rcases eq_or_ne x₁ x₂ with rfl | hx
  · have hy : y₁ ≠ (C • W).toAffine.negY x₁ y₂ := fun h ↦ hxy ⟨rfl, h⟩
    obtain rfl := Y_eq_of_Y_ne h₁ h₂ rfl hy
    have hΦy : (C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t
        ≠ W.toAffine.negY ((C.u : F) ^ 2 * x₁ + C.r)
            ((C.u : F) ^ 3 * y₁ + (C.u : F) ^ 2 * C.s * x₁ + C.t) := by
      rw [variableChange_negY]
      exact fun h ↦ hy (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination h))
    rw [W.toAffine.slope_of_Y_ne rfl hΦy, (C • W).toAffine.slope_of_Y_ne rfl hy,
      ← mul_div_assoc, div_add' _ _ _ (sub_ne_zero.mpr hy),
      div_eq_div_iff (sub_ne_zero.mpr hΦy) (sub_ne_zero.mpr hy)]
    simp [negY, variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄]
    field
  · have hΦx : (C.u : F) ^ 2 * x₁ + C.r ≠ (C.u : F) ^ 2 * x₂ + C.r := by
      simpa [mul_right_inj' (pow_ne_zero 2 hu)] using hx
    rw [W.toAffine.slope_of_X_ne hΦx, (C • W).toAffine.slope_of_X_ne hx]
    have h1 := sub_ne_zero.mpr hΦx
    have h2 := sub_ne_zero.mpr hx
    field

/-- A point `(x, y)` lies on `C • W` if and only if `(u²x + r, u³y + u²sx + t)` lies on `W`. -/
lemma variableChange_equation (x y : F) :
    W.toAffine.Equation ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ↔ (C • W).toAffine.Equation x y := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  simp only [equation_iff', variableChange_a₁, variableChange_a₂, variableChange_a₃,
    variableChange_a₄, variableChange_a₆, Units.val_inv_eq_inv_val, field]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩ <;> linear_combination h

/-- The `Y`-derivative of a Weierstrass equation under an admissible change of variables.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialY (x y : F) :
    W.toAffine.polynomialY.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y := by
  simp only [Affine.evalEval_polynomialY, variableChange_a₁, variableChange_a₃,
    Units.val_inv_eq_inv_val]
  field

/-- The `X`-derivative of a Weierstrass equation under an admissible change of variables.
The correction term is the chain-rule contribution from the `sx` term in the new `Y` coordinate.
This formula does not require either equation to be elliptic. -/
lemma variableChange_polynomialX (x y : F) :
    W.toAffine.polynomialX.evalEval ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) =
      (C.u : F) ^ 4 * (C • W).toAffine.polynomialX.evalEval x y -
        C.s * ((C.u : F) ^ 3 * (C • W).toAffine.polynomialY.evalEval x y) := by
  simp only [Affine.evalEval_polynomialX, Affine.evalEval_polynomialY, variableChange_a₁,
    variableChange_a₂, variableChange_a₃, variableChange_a₄,
    Units.val_inv_eq_inv_val]
  field

/-- An admissible change of variables identifies the nonsingular loci even when the common
Weierstrass cubic is singular. -/
lemma variableChange_nonsingular (x y : F) :
    W.toAffine.Nonsingular ((C.u : F) ^ 2 * x + C.r)
        ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t) ↔
      (C • W).toAffine.Nonsingular x y := by
  rw [Affine.Nonsingular, Affine.Nonsingular, variableChange_equation W C,
    variableChange_polynomialX W C, variableChange_polynomialY W C]
  apply and_congr_right
  intro _
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  constructor
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        intro hX
        apply hx
        rw [hY, mul_zero, mul_zero, sub_zero, hX, mul_zero]
      · exact Or.inr hY
    · exact Or.inr fun hY ↦ hy (mul_eq_zero.mpr <| Or.inr hY)
  · rintro (hx | hy)
    · by_cases hY : (C • W).toAffine.polynomialY.evalEval x y = 0
      · left
        rw [hY, mul_zero, mul_zero, sub_zero]
        exact mul_ne_zero (pow_ne_zero 4 hu) hx
      · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hY)
    · exact Or.inr (mul_ne_zero (pow_ne_zero 3 hu) hy)

/-! ### The induced isomorphism of point groups -/

namespace Point

/-- The underlying point map of the change of variables, sending `0` to `0`. -/
def mapVariableChangeFun : (C • W).toAffine.Point → W.toAffine.Point
  | .zero => .zero
  | .some x y h => .some ((C.u : F) ^ 2 * x + C.r)
      ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
      ((variableChange_nonsingular W C x y).mpr h)

@[simp] lemma mapVariableChangeFun_zero : mapVariableChangeFun W C 0 = 0 := rfl

lemma mapVariableChangeFun_some {x y : F} (h : (C • W).toAffine.Nonsingular x y) :
    mapVariableChangeFun W C (.some x y h)
      = .some ((C.u : F) ^ 2 * x + C.r) ((C.u : F) ^ 3 * y + (C.u : F) ^ 2 * C.s * x + C.t)
          ((variableChange_nonsingular W C x y).mpr h) := rfl

lemma some_eq_some (W : WeierstrassCurve F) {x₁ x₂ y₁ y₂ : F} (hx : x₁ = x₂) (hy : y₁ = y₂)
    {h₁ : W.toAffine.Nonsingular x₁ y₁} {h₂ : W.toAffine.Nonsingular x₂ y₂} :
    (some x₁ y₁ h₁ : W.toAffine.Point) = some x₂ y₂ h₂ := by
  subst hx hy
  rfl

lemma mapVariableChangeFun_injective :
    Function.Injective (mapVariableChangeFun W C) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩) h
  · rfl
  · simp [mapVariableChangeFun] at h
  · simp [mapVariableChangeFun] at h
  · rw [mapVariableChangeFun_some, mapVariableChangeFun_some] at h
    injection h with hX hY
    have hx : x₁ = x₂ := mul_left_cancel₀ (pow_ne_zero 2 hu) (by linear_combination hX)
    exact some_eq_some (C • W) hx
      (mul_left_cancel₀ (pow_ne_zero 3 hu) (by linear_combination hY - (C.u : F) ^ 2 * C.s * hx))

variable [DecidableEq F]

/-- Transport of the affine point group along an equality of Weierstrass curves. -/
def equivOfEq {V V' : WeierstrassCurve F} (h : V = V') :
    V.toAffine.Point ≃+ V'.toAffine.Point := by
  subst h
  exact AddEquiv.refl _

@[simp] lemma equivOfEq_some {V V' : WeierstrassCurve F} (h : V = V') {x y : F}
    (hns : V.toAffine.Nonsingular x y) :
    equivOfEq h (some x y hns) = some x y (h ▸ hns) := by
  subst h
  rfl

/-- The group homomorphism induced by the admissible change of variables. -/
def mapVariableChange : (C • W).toAffine.Point →+ W.toAffine.Point where
  toFun := mapVariableChangeFun W C
  map_zero' := rfl
  map_add' := by
    rintro (_ | ⟨x₁, y₁, h₁⟩) (_ | ⟨x₂, y₂, h₂⟩)
    any_goals rfl
    simp only [mapVariableChangeFun_some]
    have e₁ : (C • W).toAffine.Equation x₁ y₁ := h₁.left
    have e₂ : (C • W).toAffine.Equation x₂ y₂ := h₂.left
    by_cases hxy : x₁ = x₂ ∧ y₁ = (C • W).toAffine.negY x₂ y₂
    · rw [add_of_Y_eq hxy.1 hxy.2, mapVariableChangeFun_zero]
      refine (add_of_Y_eq ?_ ?_).symm
      · rw [hxy.1]
      · rw [variableChange_negY, hxy.2, hxy.1]
    · rw [add_some hxy, mapVariableChangeFun_some, add_some (variableChange_negY_ne W C hxy)]
      simp only [variableChange_slope W C e₁ e₂ hxy, variableChange_addX, variableChange_addY]

/-- The point-group isomorphism induced by the admissible change of variables. -/
def equivVariableChange : (C • W).toAffine.Point ≃+ W.toAffine.Point :=
  have hright : ∀ P, mapVariableChangeFun W C
      (mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)) = P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rintro (_ | ⟨X, Y, h⟩)
    · simp [← zero_def]
    · rw [equivOfEq_some, mapVariableChangeFun_some, mapVariableChangeFun_some]
      refine some_eq_some W ?_ ?_ <;>
        (simp only [VariableChange.inv_def, Units.val_inv_eq_inv_val]; field)
  { toFun := mapVariableChangeFun W C
    invFun := fun P ↦ mapVariableChangeFun (C • W) C⁻¹ (equivOfEq (inv_smul_smul C W).symm P)
    left_inv := Function.RightInverse.leftInverse_of_injective hright
      (mapVariableChangeFun_injective W C)
    right_inv := hright
    map_add' := (mapVariableChange W C).map_add' }



end Point

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

/-- The original quotient and the minimal completed-square model have
additively equivalent affine point groups. -/
def quotientToMinimalDescentEquiv :
    quotientCurve.toAffine.Point ≃+ minimalDescentCurve.toAffine.Point :=
  (WeierstrassCurve.Affine.Point.equivVariableChange
    quotientCurve quotientCurve.toCharNeTwoNF).symm

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





end

end MazurTorsion.XOneEighteenMinimalTwoDescentModel

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

open MazurTorsion.XOneEighteenMinimalTwoDescentModel
open MazurTorsion.XOneEighteenGlobalSelmerBridge (fieldSquareclass kernelRepresentative kernelRepresentative_zero)
open WeierstrassCurve.Affine (isUnit_mk_sub_X_of_eval_f_ne_zero)

private theorem minimal_affine_difference_ne_zero
    (x : MazurTorsion.XOneEighteenMinimalTwoDescentModel.K) :
    algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K
      MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM ≠ 0 := by
  have hx : minimalDescentCurve.toAffine.f.eval x ≠ 0 :=
    minimalDescentPolynomial_irreducible.not_isRoot_of_natDegree_ne_one
      (by rw [minimalDescentCurve.toAffine.natDegree_f]; norm_num)
  have hu := isUnit_mk_sub_X_of_eval_f_ne_zero hx
  have hi : minimalDescentAlgebraEquiv
      (AdjoinRoot.mk minimalDescentCurve.toAffine.f (Polynomial.C x - Polynomial.X)) =
      algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K
        MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM := by
    rw [map_sub, AdjoinRoot.mk_C, AdjoinRoot.mk_X, map_sub]
    change minimalDescentAlgebraEquiv
      (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K
        minimalDescentCurve.toAffine.A x) -
        minimalDescentAlgebraEquiv minimalGenericRoot = _
    rw [minimalDescentAlgebraEquiv.commutes, minimalDescentAlgebraEquiv_genericRoot]
  rw [← hi]
  exact (hu.map minimalDescentAlgebraEquiv.toRingHom).ne_zero

private theorem minimal_point_has_half
    (P : minimalDescentCurve.toAffine.Point) :
    ∃ Q : minimalDescentCurve.toAffine.Point, 2 • Q = P := by
  cases P with
  | zero =>
    refine ⟨0, ?_⟩
    rw [show (WeierstrassCurve.Affine.Point.zero : minimalDescentCurve.toAffine.Point) = 0 from rfl]
    exact nsmul_zero (M := minimalDescentCurve.toAffine.Point) 2
  | some x y h =>
    have hv := minimal_affine_difference_ne_zero x
    obtain ⟨mask, hm⟩ := MazurTransfer.order18_affine_point_global_kernel_mask x y h hv
    have hzero := MazurTransfer.order18_affine_point_local_kernel_mask_zero x y h hv mask hm
    rw [hzero, kernelRepresentative_zero] at hm
    have hs : IsSquare
        (algebraMap MazurTorsion.XOneEighteenMinimalTwoDescentModel.K
          MazurTorsion.XOneEighteenTwoDivisionArithmetic.M x - minimalDescentRootInM) := by
      have hs' := (_root_.Units.modPow.mk_eq_one_iff_isSquare).mp hm
      simpa only [fieldSquareclass, Units.val_mk0] using hs'
    exact MazurTransfer.order18_minimal_point_halving_of_square_difference x y h hs

private theorem doubling_surjective_of_addEquiv
    {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (h : ∀ P : B, ∃ Q : B, 2 • Q = P) :
    Function.Surjective (nsmulAddMonoidHom (α := A) 2) := by
  intro P
  obtain ⟨Q, hQ⟩ := h (e P)
  refine ⟨e.symm Q, ?_⟩
  apply e.injective
  change e (2 • e.symm Q) = _
  rw [map_nsmul, AddEquiv.apply_symm_apply]
  exact hQ

theorem solution : Function.Surjective
    (nsmulAddMonoidHom
      (α := MazurTorsion.XOneEighteenRealCubicQuotient.quotientCurve.toAffine.Point) 2) :=
  doubling_surjective_of_addEquiv quotientToMinimalDescentEquiv minimal_point_has_half

#print axioms solution
