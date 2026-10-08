-- Prove2me | solution 1 for MazurTransfer.order18_original_generator_support_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-07T16:14:15.11947+00:00
-- url     : https://prove2.me/submissions/c5aef06d-a6aa-4cc0-a0a7-bb4b2164a85c

import Mathlib
import Definitions.Def_MazurTransfer_Order18KernelGeneratorSupportCertificate
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

theorem solution : Nonempty
    MazurTorsion.XOneEighteenGlobalSelmerBridge.KernelGeneratorSupportCertificate :=
  ⟨MazurTorsion.XOneEighteenKernelGeneratorSupport.kernelGeneratorSupportCertificate⟩
#print axioms solution
