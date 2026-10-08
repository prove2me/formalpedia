-- Prove2me | solution 1 for MazurTransfer.order18_supported_selmer_cardinality_256
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T19:07:27.747154+00:00
-- url     : https://prove2.me/submissions/7ff9a79b-f5da-428e-86fa-91deaaf53511

import Mathlib
import Definitions.Def_MazurTransfer_Order18AmbientSelmer
import Theorems.Thm_MazurTransfer_order18_compositum_integers_principal
import Theorems.Thm_MazurTransfer_order18_compositum_exact_signature
import Theorems.Thm_MazurTransfer_degree_9_unit_square_index
import Theorems.Thm_MazurTransfer_order18_actual_dyadic_valuation_certificate
namespace MazurTorsion.XOneEighteenTwoDivisionSignature
end MazurTorsion.XOneEighteenTwoDivisionSignature
namespace MazurTorsion.XOneEighteenTwoDivisionDiscriminant
end MazurTorsion.XOneEighteenTwoDivisionDiscriminant


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





/-- If the ring of integers of `L` is a principal ideal domain, then the integral closure of
`𝓞 K` in `L` (being isomorphic to `𝓞 L`) has trivial class group. -/
theorem NumberField.subsingleton_classGroup_integralClosure (h : IsPrincipalIdealRing (𝓞 L)) :
    Subsingleton (ClassGroup (integralClosure (𝓞 K) L)) := by
  have : NumberField L := .of_module_finite K L
  have e : integralClosure (𝓞 K) L ≃ₐ[𝓞 K] 𝓞 L :=
    IsIntegralClosure.equiv (𝓞 K) (integralClosure (𝓞 K) L) L (𝓞 L)
  have : IsPrincipalIdealRing (integralClosure (𝓞 K) L) :=
    IsPrincipalIdealRing.of_surjective e.symm.toRingEquiv.toRingHom e.symm.surjective
  exact Fintype.card_le_one_iff_subsingleton.mp card_classGroup_eq_one.le



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

















/-! ## The two incompatible cubic discriminants -/







/-! ## Linear disjointness of the two rational cubic fields -/











/-- The compositum has degree nine over `ℚ`. -/
theorem finrank_M_over_rat : Module.finrank ℚ M = 9 := by
  exact MazurTransfer.order18_compositum_exact_signature.1


end

end MazurTorsion.XOneEighteenTwoDivisionClassNumber

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenTwoDivisionExactSignature. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The exact signature of the `X₁(18)` two-division compositum

The compositum has degree nine, at most three real places, and an odd
number of complex places.  The signature identity

`r₁ + 2 r₂ = 9`

then forces `(r₁, r₂) = (3, 3)`.
-/

open Module NumberField NumberField.InfinitePlace

namespace MazurTorsion.XOneEighteenTwoDivisionExactSignature

noncomputable section

open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionClassNumber
open MazurTorsion.XOneEighteenTwoDivisionSignature
open MazurTorsion.XOneEighteenTwoDivisionDiscriminant



/-- The degree-nine compositum has exactly three real places. -/
theorem nrRealPlaces_eq_three : nrRealPlaces M = 3 := by
  exact MazurTransfer.order18_compositum_exact_signature.2.1




end

end MazurTorsion.XOneEighteenTwoDivisionExactSignature

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







private lemma eq_one_or_parityOne (z : Multiplicative (ZMod 2)) :
    z = 1 ∨ z = parityOne := by
  cases z with
  | ofAdd z =>
      fin_cases z
      · left
        apply Multiplicative.toAdd.injective
        rfl
      · right
        rfl

/-- Two supported squareclasses whose valuation parities form the identity
matrix generate every two-prime parity vector.  The equivalence `places`
is itself a checked assertion that the support consists of exactly two
primes. -/
theorem supportValuation_surjective_of_two_generators
    (places : Fin 2 ≃ S)
    (g₀ g₁ : SupportedSelmer (R := R) (K := K) S 2)
    (hg₀₀ : supportValuation (R := R) (K := K) S 2 g₀ (places 0) = parityOne)
    (hg₀₁ : supportValuation (R := R) (K := K) S 2 g₀ (places 1) = 1)
    (hg₁₀ : supportValuation (R := R) (K := K) S 2 g₁ (places 0) = 1)
    (hg₁₁ : supportValuation (R := R) (K := K) S 2 g₁ (places 1) = parityOne) :
    Function.Surjective (supportValuation (R := R) (K := K) S 2) := by
  intro y
  rcases eq_one_or_parityOne (y (places 0)) with h₀ | h₀ <;>
    rcases eq_one_or_parityOne (y (places 1)) with h₁ | h₁
  · refine ⟨1, ?_⟩
    funext s
    obtain ⟨i, rfl⟩ := places.surjective s
    fin_cases i <;> simp [h₀, h₁]
  · refine ⟨g₁, ?_⟩
    funext s
    obtain ⟨i, rfl⟩ := places.surjective s
    fin_cases i
    · simp [hg₁₀, h₀]
    · simp [hg₁₁, h₁]
  · refine ⟨g₀, ?_⟩
    funext s
    obtain ⟨i, rfl⟩ := places.surjective s
    fin_cases i
    · simp [hg₀₀, h₀]
    · simp [hg₀₁, h₁]
  · refine ⟨g₀ * g₁, ?_⟩
    funext s
    obtain ⟨i, rfl⟩ := places.surjective s
    fin_cases i
    · calc
        supportValuation (R := R) (K := K) S 2 (g₀ * g₁) (places 0) =
            supportValuation (R := R) (K := K) S 2 g₀ (places 0) *
              supportValuation (R := R) (K := K) S 2 g₁ (places 0) := by
                rw [map_mul, Pi.mul_apply]
        _ = parityOne * 1 := congrArg₂ (fun a b ↦ a * b) hg₀₀ hg₁₀
        _ = parityOne := mul_one _
        _ = y (places 0) := h₀.symm
    · calc
        supportValuation (R := R) (K := K) S 2 (g₀ * g₁) (places 1) =
            supportValuation (R := R) (K := K) S 2 g₀ (places 1) *
              supportValuation (R := R) (K := K) S 2 g₁ (places 1) := by
                rw [map_mul, Pi.mul_apply]
        _ = 1 * parityOne := congrArg₂ (fun a b ↦ a * b) hg₀₁ hg₁₁
        _ = parityOne := one_mul _
        _ = y (places 1) := h₁.symm

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







/-- A degree-nine number field of signature `(3,3)` has exactly `64`
integral-unit square classes. -/
theorem natCard_unitsModSq_of_degree_nine_of_nrRealPlaces_eq_three
    (hdegree : Module.finrank ℚ L = 9)
    (hreal : nrRealPlaces L = 3) :
    Nat.card (Units.modPow (𝓞 L) 2) = 64 := by
  exact MazurTransfer.degree_9_unit_square_index L hdegree hreal


/-! ## The totally real cubic coefficient field -/









end

end MazurTorsion.XOneEighteenDescent

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







private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

















































end

end MazurTorsion.XOneEighteenCoefficientDyadicSelmer

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













/-- The integral closure used by the relative descent has exactly `64`
unit square classes. -/
theorem natCard_relativeUnitsModSq :
    Nat.card (Units.modPow RelativeIntegers 2) = 64 := by
  rw [Nat.card_congr relativeUnitSquareclassEquiv.toEquiv]
  exact
    MazurTorsion.XOneEighteenDescent.natCard_unitsModSq_of_degree_nine_of_nrRealPlaces_eq_three
      M finrank_M_over_rat nrRealPlaces_eq_three

/-! ## The exact dyadic support -/





/-! ## The minimal model has genuinely dyadic bad support -/



















/-! ## Relative norm and its four checked kernel generators -/







































/-! ## Cardinality from genuine arithmetic certificates -/



/-- The valuation matrix gives every parity vector at the two dyadic
primes. -/
theorem DyadicValuationCertificate.surjective
    (C : DyadicValuationCertificate) :
    Function.Surjective
      (supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2) :=
  supportValuation_surjective_of_two_generators
    (R := RelativeIntegers) (K := M) compositumDyadicSupport
      C.places ⟨alphaSquareclass, C.alpha_mem⟩
        ⟨betaSquareclass, C.beta_mem⟩ C.alpha_at_zero C.alpha_at_one
        C.beta_at_zero C.beta_at_one



/-! ## The actual ambient relative norm -/















/-- The dyadic Selmer group of the degree-nine field has cardinality
`256`, from the checked two-place valuation certificate and the relative
integral-unit calculation. -/
theorem natCard_dyadicSelmerM
    (hprincipal : IsPrincipalIdealRing (𝓞 M))
    (V : DyadicValuationCertificate) :
    Nat.card DyadicSelmerM = 256 := by
  letI : Subsingleton (ClassGroup RelativeIntegers) :=
    NumberField.subsingleton_classGroup_integralClosure K M hprincipal
  have hsupport : Nat.card compositumDyadicSupport = 2 := by
    simpa using (Nat.card_congr V.places).symm
  letI : Finite compositumDyadicSupport :=
    Nat.finite_of_card_ne_zero (hsupport.trans_ne (by norm_num))
  letI : Fact (0 < (2 : ℕ)) := ⟨by norm_num⟩
  letI : NeZero (2 : ℕ) := ⟨by norm_num⟩
  letI : Finite (Units.modPow RelativeIntegers 2) :=
    Nat.finite_of_card_ne_zero
      (natCard_relativeUnitsModSq.trans_ne (by norm_num))
  have hempty :
      Nat.card
          (selmerGroup (R := RelativeIntegers) (K := M)
            (S := (∅ : Set (HeightOneSpectrum RelativeIntegers)))
            (n := 2)) = 64 :=
    (natCard_emptySelmer_eq_unitsModPow
      (R := RelativeIntegers) (K := M) 2).trans
        natCard_relativeUnitsModSq
  letI : Finite
      (selmerGroup (R := RelativeIntegers) (K := M)
        (S := (∅ : Set (HeightOneSpectrum RelativeIntegers)))
        (n := 2)) :=
    Nat.finite_of_card_ne_zero (hempty.trans_ne (by norm_num))
  rw [natCard_supportedSelmer_eq_of_valuation_surjective
    (R := RelativeIntegers) (K := M) compositumDyadicSupport 2
      V.surjective,
    hempty, hsupport]
  norm_num









/-! ## The global subgroup consumed by the Selmer sieve -/





/-! ## The unique generic descent factor -/











/-! ## Integral-closure transport for the unique factor -/































end

end MazurTorsion.XOneEighteenGlobalSelmerBridge

end

theorem solution :
Nat.card MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicSelmerM = 256 := by
  exact MazurTorsion.XOneEighteenGlobalSelmerBridge.natCard_dyadicSelmerM
    MazurTransfer.order18_compositum_integers_principal
    (Classical.choice MazurTransfer.order18_actual_dyadic_valuation_certificate)

#print axioms solution
