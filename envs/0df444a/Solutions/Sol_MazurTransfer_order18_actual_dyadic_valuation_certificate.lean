-- Prove2me | solution 1 for MazurTransfer.order18_actual_dyadic_valuation_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:53:44.720195+00:00
-- url     : https://prove2.me/submissions/560053c9-a1cb-4ddc-9370-08d17439986e

import Mathlib
import Definitions.Def_MazurTransfer_Order18AmbientSelmer


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















/-- The polynomial `T³ - 3T - 1` is irreducible over `ℚ`. -/
theorem cubicPolynomial_irreducible : Irreducible cubicPolynomial := by
  exact MazurTransfer.order18_rational_cubics_irreducible.1








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













/-- A rational scalar cannot cancel the cubic generator. -/
theorem rational_add_tau_ne_zero (x : ℚ) : (x : K) + tau ≠ 0 := by
  intro h
  have htau : tau = -(x : K) := eq_neg_of_add_eq_zero_right h
  have htauc : tau ^ 3 - 3 * tau - 1 = 0 := by
    linear_combination tau_cubic
  rw [htau] at htauc
  have hxrel : (-x) ^ 3 - 3 * (-x) - 1 = 0 := by
    exact_mod_cast htauc
  have hroot : cubicPolynomial.IsRoot (-x) := by
    simpa [cubicPolynomial, Polynomial.IsRoot] using hxrel
  have hdegree : cubicPolynomial.natDegree = 3 := by
    simp only [cubicPolynomial]
    compute_degree!
  exact cubicPolynomial_irreducible.not_isRoot_of_natDegree_ne_one
    (by omega) hroot







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

/-- The first explicit dyadic generator has relative norm `2`. -/
theorem norm_alpha : Algebra.norm Q.K alpha = 2 := by
  rw [alpha, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

/-- The second explicit dyadic generator has relative norm `2(τ+1)`. -/
theorem norm_beta : Algebra.norm Q.K beta = 2 * Q.tau + 2 := by
  rw [beta, norm_quadraticElement]
  field_simp
  ring_nf
  simp only [tau_pow_six, tau_pow_five, tau_pow_four, Q.tau_cubic]
  ring

















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
def MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis : PowerBasis ℚ Q.K :=
  AdjoinRoot.powerBasis' coefficientPolynomial_monic





theorem coefficientPowerBasis_minpolyGen :
    MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.minpolyGen = Q.cubicPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval Q.tau Q.cubicPolynomial = 0 := by
    simp only [Q.cubicPolynomial,
      MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
      map_sub, map_pow, aeval_X, map_mul, map_ofNat, map_one]
    linear_combination Q.tau_cubic
  exact (minpoly.eq_of_irreducible_of_monic Q.cubicPolynomial_irreducible
    hroot coefficientPolynomial_monic).symm



theorem MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim : MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.dim = 3 := by
  rw [MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis, AdjoinRoot.powerBasis'_dim]
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
    Algebra.discr ℚ MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.basis = 81 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank, MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, coefficientPowerBasis_minpolyGen]
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
    derivative_sub, derivative_pow, derivative_X, derivative_mul,
    derivative_ofNat, derivative_one, mul_one, Nat.cast_ofNat,
    zero_mul, sub_zero]
  rw [show MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.gen = Q.tau by rfl]
  have hnorm := norm_cubic_derivative MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis
    MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim 1 (by
      simpa only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
        C_1] using coefficientPowerBasis_minpolyGen)
  rw [show MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.gen = Q.tau by rfl] at hnorm
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
  apply integer_discriminant_mem_conductor MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis
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

/-- The normalized generator as an element of the full ring of integers. -/
def normalizedInteger : NumberField.RingOfIntegers M :=
  ⟨normalizedElement, normalizedElement_isIntegral_int⟩

@[simp]
theorem normalizedInteger_coe :
    (normalizedInteger : M) = normalizedElement := rfl

theorem normalizedInteger_aeval :
    Polynomial.aeval normalizedInteger normalizedPolynomialInt = 0 := by
  rw [← RingOfIntegers.coe_eq_zero_iff]
  rw [Polynomial.aeval_def, Polynomial.hom_eval₂]
  simpa only [← IsScalarTower.algebraMap_eq ℤ
      (NumberField.RingOfIntegers M) M, normalizedInteger_coe,
    ← Polynomial.aeval_def] using normalizedPolynomialInt_aeval





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

/-- Integer polynomial representing `alpha`. -/
def alphaPolynomialInt : Polynomial ℤ :=
  X * (X ^ 7 - 3 * X ^ 6 + 7 * X ^ 4 - 3 * X ^ 3 -
    9 * X ^ 2 + 4 * X + 5)

private def alphaPolynomial : Polynomial ℚ :=
  X * (X ^ 7 - 3 * X ^ 6 + 7 * X ^ 4 - 3 * X ^ 3 -
    9 * X ^ 2 + 4 * X + 5)

theorem alphaPolynomialInt_map :
    alphaPolynomialInt.map (algebraMap ℤ ℚ) = alphaPolynomial := by
  norm_num [alphaPolynomialInt, alphaPolynomial]

private def alphaNumerator : Polynomial ℚ :=
  (2 * coefficientPolynomial ^ 2 - coefficientPolynomial - 1) *
      relativePolynomialInNormalized ^ 2 +
    (-4 * coefficientPolynomial ^ 2 - coefficientPolynomial + 11) *
      relativePolynomialInNormalized +
    (-4 * coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 14)

private def alphaReductionQuotient : Polynomial ℚ :=
  2 * X ^ 23 - 26 * X ^ 22 + 150 * X ^ 21 - 492 * X ^ 20 +
    946 * X ^ 19 - 848 * X ^ 18 - 494 * X ^ 17 + 2212 * X ^ 16 -
    1759 * X ^ 15 - 1699 * X ^ 14 + 4642 * X ^ 13 -
    3073 * X ^ 12 - 1526 * X ^ 11 + 3832 * X ^ 10 -
    1816 * X ^ 9 - 1428 * X ^ 8 + 2503 * X ^ 7 - 1325 * X ^ 6 -
    126 * X ^ 5 + 587 * X ^ 4 - 316 * X ^ 3 + 14 * X ^ 2 +
    78 * X - 50

private theorem alpha_reduction_identity :
    alphaNumerator = 18 * alphaPolynomial +
      alphaReductionQuotient * normalizedPolynomial := by
  simp only [alphaNumerator, alphaPolynomial, alphaReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem alpha_formula_rat :
    alpha = Polynomial.aeval normalizedElement alphaPolynomial := by
  calc
    alpha = (1 / 18 : M) *
        Polynomial.aeval normalizedElement alphaNumerator := by
      rw [alpha, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_one, map_neg]
      change ((2 * t ^ 2 - t - 1) / 18) * s ^ 2 +
          ((-4 * t ^ 2 - t + 11) / 18) * s +
          ((-4 * t ^ 2 + 2 * t + 14) / 18) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [alphaNumerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_one, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement alphaPolynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        alpha_reduction_identity

/-- The first dyadic generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem alpha_formula :
    alpha = Polynomial.aeval normalizedElement alphaPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    alphaPolynomialInt, alphaPolynomialInt_map]
  exact alpha_formula_rat

/-- Integer polynomial representing `beta`. -/
def betaPolynomialInt : Polynomial ℤ :=
  -(X - 2) * (2 * X ^ 7 - 3 * X ^ 6 - X ^ 5 + 6 * X ^ 4 +
    X ^ 3 - 4 * X ^ 2 + 1)

private def betaPolynomial : Polynomial ℚ :=
  -(X - 2) * (2 * X ^ 7 - 3 * X ^ 6 - X ^ 5 + 6 * X ^ 4 +
    X ^ 3 - 4 * X ^ 2 + 1)

theorem betaPolynomialInt_map :
    betaPolynomialInt.map (algebraMap ℤ ℚ) = betaPolynomial := by
  norm_num [betaPolynomialInt, betaPolynomial]

private def betaNumerator : Polynomial ℚ :=
  (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 2) *
      relativePolynomialInNormalized ^ 2 +
    (-coefficientPolynomial ^ 2 + 2 * coefficientPolynomial + 8) *
      relativePolynomialInNormalized +
    (8 * coefficientPolynomial ^ 2 + 8 * coefficientPolynomial - 10)

private def betaReductionQuotient : Polynomial ℚ :=
  -X ^ 23 + 13 * X ^ 22 - 75 * X ^ 21 + 246 * X ^ 20 -
    473 * X ^ 19 + 424 * X ^ 18 + 247 * X ^ 17 - 1106 * X ^ 16 +
    881 * X ^ 15 + 836 * X ^ 14 - 2267 * X ^ 13 +
    1412 * X ^ 12 + 937 * X ^ 11 - 2042 * X ^ 10 + 881 * X ^ 9 +
    888 * X ^ 8 - 1403 * X ^ 7 + 580 * X ^ 6 + 387 * X ^ 5 -
    610 * X ^ 4 + 266 * X ^ 3 + 35 * X ^ 2 - 96 * X + 40

private theorem beta_reduction_identity :
    betaNumerator = 18 * betaPolynomial +
      betaReductionQuotient * normalizedPolynomial := by
  simp only [betaNumerator, betaPolynomial, betaReductionQuotient,
    coefficientPolynomial, relativePolynomialInNormalized,
    normalizedPolynomial]
  ring

private theorem beta_formula_rat :
    beta = Polynomial.aeval normalizedElement betaPolynomial := by
  calc
    beta = (1 / 18 : M) *
        Polynomial.aeval normalizedElement betaNumerator := by
      rw [beta, quadraticElement_eq]
      simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat,
        map_neg]
      change ((-t ^ 2 + 2 * t + 2) / 18) * s ^ 2 +
          ((-t ^ 2 + 2 * t + 8) / 18) * s +
          ((8 * t ^ 2 + 8 * t - 10) / 18) = _
      rw [coefficientGenerator_formula, relativeGenerator_formula]
      simp only [betaNumerator, map_add, map_sub, map_mul, map_pow,
        map_ofNat, map_neg]
      ring
    _ = Polynomial.aeval normalizedElement betaPolynomial := by
      exact scaled_aeval_of_reduction 18 (by norm_num)
        beta_reduction_identity

/-- The second dyadic generator is the value of an integer polynomial in the
normalized algebraic integer. -/
theorem beta_formula :
    beta = Polynomial.aeval normalizedElement betaPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    betaPolynomialInt, betaPolynomialInt_map]
  exact beta_formula_rat















































































/-- Integer polynomial representing the integral quotient
`beta² * alpha / 2`. -/
def dyadicQuotientPolynomialInt : Polynomial ℤ :=
  -2 * X ^ 8 + 6 * X ^ 7 - 2 * X ^ 6 - 9 * X ^ 5 +
    7 * X ^ 4 + 8 * X ^ 3 - 3 * X ^ 2 - X + 1

private def dyadicQuotientPolynomial : Polynomial ℚ :=
  -2 * X ^ 8 + 6 * X ^ 7 - 2 * X ^ 6 - 9 * X ^ 5 +
    7 * X ^ 4 + 8 * X ^ 3 - 3 * X ^ 2 - X + 1

theorem dyadicQuotientPolynomialInt_map :
    dyadicQuotientPolynomialInt.map (algebraMap ℤ ℚ) =
      dyadicQuotientPolynomial := by
  norm_num [dyadicQuotientPolynomialInt, dyadicQuotientPolynomial]

private def dyadicQuotientReduction : Polynomial ℚ :=
  4 * X ^ 15 - 28 * X ^ 14 + 69 * X ^ 13 - 38 * X ^ 12 -
    131 * X ^ 11 + 210 * X ^ 10 + 74 * X ^ 9 - 364 * X ^ 8 +
    120 * X ^ 7 + 278 * X ^ 6 - 173 * X ^ 5 - 110 * X ^ 4 +
    97 * X ^ 3 + 10 * X ^ 2 - 22 * X + 2

private theorem dyadicQuotient_reduction_identity :
    betaPolynomial ^ 2 * alphaPolynomial =
      2 * dyadicQuotientPolynomial +
        dyadicQuotientReduction * normalizedPolynomial := by
  simp only [betaPolynomial, alphaPolynomial, dyadicQuotientPolynomial,
    dyadicQuotientReduction, normalizedPolynomial]
  ring

private theorem beta_sq_mul_alpha_div_two_formula_rat :
    beta ^ 2 * alpha / 2 =
      Polynomial.aeval normalizedElement dyadicQuotientPolynomial := by
  calc
    beta ^ 2 * alpha / 2 = (1 / 2 : M) *
        Polynomial.aeval normalizedElement
          (betaPolynomial ^ 2 * alphaPolynomial) := by
      rw [beta_formula_rat, alpha_formula_rat]
      simp only [map_mul, map_pow]
      ring
    _ = Polynomial.aeval normalizedElement dyadicQuotientPolynomial := by
      exact scaled_aeval_of_reduction 2 (by norm_num)
        dyadicQuotient_reduction_identity

theorem beta_sq_mul_alpha_div_two_formula :
    beta ^ 2 * alpha / 2 =
      Polynomial.aeval normalizedElement dyadicQuotientPolynomialInt := by
  rw [← Polynomial.aeval_map_algebraMap (ℚ) normalizedElement
    dyadicQuotientPolynomialInt, dyadicQuotientPolynomialInt_map]
  exact beta_sq_mul_alpha_div_two_formula_rat















private theorem normalized_aeval_isIntegral (p : Polynomial ℤ) :
    IsIntegral ℤ (Polynomial.aeval normalizedElement p) := by
  rw [← mem_integralClosure_iff]
  have hv : normalizedElement ∈ integralClosure ℤ M :=
    normalizedElement_isIntegral_int
  have hle : Algebra.adjoin ℤ ({normalizedElement} : Set M) ≤
      integralClosure ℤ M :=
    Algebra.adjoin_le (Set.singleton_subset_iff.mpr hv)
  exact hle (Polynomial.aeval_mem_adjoin_singleton ℤ normalizedElement)

theorem alpha_isIntegral : IsIntegral ℤ alpha := by
  rw [alpha_formula]
  exact normalized_aeval_isIntegral alphaPolynomialInt

theorem beta_isIntegral : IsIntegral ℤ beta := by
  rw [beta_formula]
  exact normalized_aeval_isIntegral betaPolynomialInt











theorem beta_sq_mul_alpha_div_two_isIntegral :
    IsIntegral ℤ (beta ^ 2 * alpha / 2) := by
  rw [beta_sq_mul_alpha_div_two_formula]
  exact normalized_aeval_isIntegral dyadicQuotientPolynomialInt



/-- The first dyadic generator in the full ring of integers. -/
def alphaInteger : NumberField.RingOfIntegers M := ⟨alpha, alpha_isIntegral⟩

/-- The second dyadic generator in the full ring of integers. -/
def betaInteger : NumberField.RingOfIntegers M := ⟨beta, beta_isIntegral⟩











/-- The integral quotient `beta² * alpha / 2`. -/
def dyadicQuotientInteger : NumberField.RingOfIntegers M :=
  ⟨beta ^ 2 * alpha / 2, beta_sq_mul_alpha_div_two_isIntegral⟩



@[simp] theorem alphaInteger_coe : (alphaInteger : M) = alpha := rfl
@[simp] theorem betaInteger_coe : (betaInteger : M) = beta := rfl





@[simp] theorem dyadicQuotientInteger_coe :
    (dyadicQuotientInteger : M) = beta ^ 2 * alpha / 2 := rfl


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

/-- An inverse of `beta^2 * alpha / 2` in the normalized integral order. -/
def dyadicQuotientInversePolynomialInt : Polynomial ℤ :=
  4 * X ^ 8 - 14 * X ^ 7 + 7 * X ^ 6 + 25 * X ^ 5 -
    26 * X ^ 4 - 22 * X ^ 3 + 24 * X ^ 2 + 10 * X - 5

private def dyadicQuotientBezoutPolynomialInt : Polynomial ℤ :=
  -8 * X ^ 7 + 28 * X ^ 6 - 22 * X ^ 5 - 26 * X ^ 4 +
    44 * X ^ 3 + 7 * X ^ 2 - 15 * X + 6

private theorem dyadicQuotient_bezout_identity :
    dyadicQuotientPolynomialInt * dyadicQuotientInversePolynomialInt =
      1 + dyadicQuotientBezoutPolynomialInt * normalizedPolynomialInt := by
  simp only [dyadicQuotientPolynomialInt,
    dyadicQuotientInversePolynomialInt,
    dyadicQuotientBezoutPolynomialInt, normalizedPolynomialInt]
  ring

/-- The explicit inverse of the dyadic quotient in the full ring of
integers. -/
def dyadicQuotientInverseInteger : NumberField.RingOfIntegers M :=
  Polynomial.aeval normalizedInteger dyadicQuotientInversePolynomialInt

private theorem dyadicQuotientInteger_eq_aeval :
    dyadicQuotientInteger =
      Polynomial.aeval normalizedInteger dyadicQuotientPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change (dyadicQuotientInteger : M) =
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      (Polynomial.aeval normalizedInteger dyadicQuotientPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ (NumberField.RingOfIntegers M) M)
      normalizedInteger dyadicQuotientPolynomialInt]
  simpa only [dyadicQuotientInteger_coe, normalizedInteger_coe,
    IsScalarTower.toAlgHom_apply] using beta_sq_mul_alpha_div_two_formula

theorem dyadicQuotientInteger_mul_inverse :
    dyadicQuotientInteger * dyadicQuotientInverseInteger = 1 := by
  rw [dyadicQuotientInteger_eq_aeval, dyadicQuotientInverseInteger,
    ← map_mul, dyadicQuotient_bezout_identity]
  simp only [map_add, map_one, map_mul, normalizedInteger_aeval,
    mul_zero, add_zero]

/-- The integral quotient `beta^2 * alpha / 2` is a unit. -/
theorem dyadicQuotientInteger_isUnit : IsUnit dyadicQuotientInteger := by
  exact ⟨⟨dyadicQuotientInteger, dyadicQuotientInverseInteger,
    dyadicQuotientInteger_mul_inverse,
    by rw [mul_comm, dyadicQuotientInteger_mul_inverse]⟩, rfl⟩















/-! ## Exact principal-ideal factorizations -/

private theorem dyadic_element_factorization :
    betaInteger ^ 2 * alphaInteger =
      dyadicQuotientInteger * (2 : NumberField.RingOfIntegers M) := by
  apply RingOfIntegers.coe_injective
  simp only [map_mul, map_pow, betaInteger_coe, alphaInteger_coe,
    dyadicQuotientInteger_coe, map_ofNat]
  field_simp

/-- Exact factorization of the rational dyadic ideal in the compositum. -/
theorem span_two_eq_span_alpha_mul_span_beta_sq :
    Ideal.span {(2 : NumberField.RingOfIntegers M)} =
      Ideal.span {alphaInteger} * Ideal.span {betaInteger} ^ 2 := by
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton,
    mul_comm alphaInteger (betaInteger ^ 2), dyadic_element_factorization]
  exact (Ideal.span_singleton_mul_left_unit dyadicQuotientInteger_isUnit 2).symm





/-! ## Absolute norms of the three generators -/

private theorem coefficientField_finrank : Module.finrank ℚ Q.K = 3 := by
  rw [MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank, MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim]

private theorem absolute_norm_alpha : Algebra.norm ℚ alpha = 8 := by
  rw [← Algebra.norm_norm (R := ℚ) (S := Q.K), norm_alpha]
  change Algebra.norm ℚ (algebraMap ℚ Q.K 2) = 8
  rw [Algebra.norm_algebraMap, coefficientField_finrank]
  norm_num

private theorem integer_norm_alphaInteger :
    Algebra.norm ℤ alphaInteger = 8 := by
  apply Rat.intCast_inj.mp
  rw [Algebra.coe_norm_int]
  simpa only [alphaInteger_coe, Int.cast_ofNat] using absolute_norm_alpha

/-- The first dyadic principal ideal has absolute norm `8`. -/
theorem absNorm_span_alpha :
    Ideal.absNorm (Ideal.span {alphaInteger}) = 8 := by
  rw [Ideal.absNorm_span_singleton, integer_norm_alphaInteger]
  norm_num

/-- The second dyadic principal ideal also has absolute norm `8`. -/
theorem absNorm_span_beta :
    Ideal.absNorm (Ideal.span {betaInteger}) = 8 := by
  have htwo : Ideal.absNorm
      (Ideal.span {(2 : NumberField.RingOfIntegers M)}) = 512 := by
    calc
      Ideal.absNorm
          (Ideal.span {(2 : NumberField.RingOfIntegers M)}) =
        2 ^ Module.finrank ℤ (NumberField.RingOfIntegers M) := by
          simpa using
            (Ideal.absNorm_span_natCast
              (S := NumberField.RingOfIntegers M) 2)
      _ = 512 := by
        rw [RingOfIntegers.rank, finrank_M_over_rat]
        norm_num
  have h := congrArg Ideal.absNorm span_two_eq_span_alpha_mul_span_beta_sq
  rw [htwo, map_mul, map_pow, absNorm_span_alpha] at h
  have hpow : Ideal.absNorm (Ideal.span {betaInteger}) ^ 2 = 8 ^ 2 := by
    norm_num at h ⊢
    omega
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) hpow



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

/-- Every prime of the compositum above `2` has inertia degree at least
three. -/
theorem compositum_inertiaDeg_ge_three_at_two
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    3 ≤ P.inertiaDeg ℤ := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  let QP : Ideal (NumberField.RingOfIntegers Q.K) :=
    P.under (NumberField.RingOfIntegers Q.K)
  have hQP : QP ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers Q.K) := ⟨inferInstance, inferInstance⟩
  have hdegree : QP.inertiaDeg ℤ = 3 :=
    coefficient_inertiaDeg_eq_three_at_two QP hQP
  have htower := Ideal.inertiaDeg_tower (R := ℤ) QP P
  rw [hdegree] at htower
  exact Nat.le_of_dvd (P.inertiaDeg_pos ℤ)
    ⟨P.inertiaDeg (NumberField.RingOfIntegers Q.K), htower⟩

/-- Every prime of the compositum above `2` has absolute norm at least
`8`. -/
theorem eight_le_absNorm_of_mem_primesOver_two
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    8 ≤ P.absNorm := by
  letI : P.IsPrime := hP.1
  letI : P.LiesOver (Ideal.span {(2 : ℤ)}) := hP.2
  rw [← Ideal.pow_inertiaDeg 2 P]
  exact pow_le_pow_right' (by norm_num : 1 ≤ (2 : ℕ))
    (compositum_inertiaDeg_ge_three_at_two P hP)

private theorem eq_of_dvd_of_eight_le_absNorm
    {P I : Ideal (NumberField.RingOfIntegers M)}
    (hdiv : P ∣ I) (hP : 8 ≤ P.absNorm) (hI : I.absNorm = 8) :
    P = I := by
  have hle : I ≤ P := Ideal.dvd_iff_le.mp hdiv
  have hnormDvd : P.absNorm ∣ I.absNorm :=
    Ideal.absNorm_dvd_absNorm_of_le hle
  have hPupper : P.absNorm ≤ 8 := by
    rw [← hI]
    exact Nat.le_of_dvd (hI.symm ▸ by norm_num) hnormDvd
  have hPnorm : P.absNorm = 8 := le_antisymm hPupper hP
  obtain ⟨J, hJ⟩ := hdiv
  have hnorm := congrArg Ideal.absNorm hJ
  rw [map_mul, hPnorm, hI] at hnorm
  have hJnorm : J.absNorm = 1 := by omega
  have hJtop : J = ⊤ := Ideal.absNorm_eq_one_iff.mp hJnorm
  rw [hJtop, mul_top] at hJ
  exact hJ.symm

/-- The two displayed principal ideals are all the primes of the compositum
above `2`. -/
theorem prime_over_two_eq_span_alpha_or_beta
    (P : Ideal (NumberField.RingOfIntegers M))
    (hP : P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)})
      (NumberField.RingOfIntegers M)) :
    P = Ideal.span {alphaInteger} ∨ P = Ideal.span {betaInteger} := by
  have hprime : Prime P :=
    Ideal.prime_of_mem_primesOver (by norm_num) hP
  letI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  have hPtwo : P ∣ Ideal.span
      {(2 : NumberField.RingOfIntegers M)} := by
    have hmap :=
      (Ideal.liesOver_iff_dvd_map hP.1.ne_top).mp hP.2
    simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using hmap
  have hprod : P ∣
      Ideal.span {alphaInteger} * Ideal.span {betaInteger} ^ 2 := by
    rw [← span_two_eq_span_alpha_mul_span_beta_sq]
    exact hPtwo
  have hlower := eight_le_absNorm_of_mem_primesOver_two P hP
  rcases hprime.dvd_or_dvd hprod with hAlpha | hBetaSq
  · exact Or.inl
      (eq_of_dvd_of_eight_le_absNorm hAlpha hlower absNorm_span_alpha)
  · have hBeta : P ∣ Ideal.span {betaInteger} :=
      hprime.dvd_of_dvd_pow hBetaSq
    exact Or.inr
      (eq_of_dvd_of_eight_le_absNorm hBeta hlower absNorm_span_beta)

end

end MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes

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
  rw [MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis.finrank, MazurTorsion.XOneEighteenTwoDivisionSmallPrimes.coefficientPowerBasis_dim]



































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















/-! ## The exact dyadic support -/





/-! ## The minimal model has genuinely dyadic bad support -/



















/-! ## Relative norm and its four checked kernel generators -/



















private theorem alpha_ne_zero : alpha ≠ 0 := by
  intro hz
  have h : Algebra.norm K alpha = 0 := Algebra.norm_eq_zero_iff.mpr hz
  rw [norm_alpha] at h
  norm_num at h

private theorem beta_ne_zero : beta ≠ 0 := by
  intro hz
  have h : Algebra.norm K beta = 0 := Algebra.norm_eq_zero_iff.mpr hz
  rw [norm_beta] at h
  have htau : Q.tau + 1 ≠ 0 := by
    have ht :=
      MazurTorsion.XOneEighteenRealCubicQuotient.rational_add_tau_ne_zero
        (1 : ℚ)
    change (1 : K) + Q.tau ≠ 0 at ht
    simpa only [add_comm] using ht
  apply htau
  linear_combination (1 / 2) * h

















/-! ## Cardinality from genuine arithmetic certificates -/







/-! ## The actual ambient relative norm -/

























/-! ## The global subgroup consumed by the Selmer sieve -/





/-! ## The unique generic descent factor -/











/-! ## Integral-closure transport for the unique factor -/































end

end MazurTorsion.XOneEighteenGlobalSelmerBridge

end


/- Source module: MazurTorsion.NumberTheory.XOneEighteenDyadicValuationCertificate. Original headers retained. -/
section
/-
Copyright (c) 2026 Vasily Ilin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasily Ilin, OpenAI
-/



/-!
# The two dyadic valuations in the `X₁(18)` two-division field

This file turns the checked ideal factorization

`(2) = (alpha) * (beta)^2`

into the exact two-place valuation certificate used by the global Selmer
enumeration.  An explicit polynomial Bezout identity modulo `2` first
separates the two displayed ideals; primality and exhaustiveness then follow
from the already checked inertia lower bound and absolute norms.
-/

open Polynomial NumberField

namespace MazurTorsion.XOneEighteenDyadicValuationCertificate

noncomputable section

open EllipticCurves.X18SelmerCardinality
open MazurTorsion.XOneEighteenCoefficientDyadicSelmer
open MazurTorsion.XOneEighteenGlobalSelmerBridge
open MazurTorsion.XOneEighteenTwoDivisionArithmetic
open MazurTorsion.XOneEighteenTwoDivisionIntegralElements
open MazurTorsion.XOneEighteenTwoDivisionIntegralModel
open MazurTorsion.XOneEighteenTwoDivisionPrincipalSmallPrimes
open MazurTorsion.XOneEighteenTwoDivisionSmallPrimes
open IsDedekindDomain Ideal RingOfIntegers UniqueFactorizationMonoid

private abbrev K := MazurTorsion.XOneEighteenGlobalSelmerBridge.K

private instance : Fact (Nat.Prime 2) := ⟨by norm_num⟩

private abbrev OM := NumberField.RingOfIntegers M

private abbrev alphaIdeal : Ideal OM := Ideal.span {alphaInteger}

private abbrev betaIdeal : Ideal OM := Ideal.span {betaInteger}

/-! ## A checked Bezout separation of the two ideals -/

private def alphaBezoutPolynomial : Polynomial ℤ :=
  X ^ 7 + X ^ 6 + X ^ 3 + 1

private def betaBezoutPolynomial : Polynomial ℤ :=
  X ^ 8 + X ^ 7 + X ^ 4 + X

private def relationBezoutPolynomial : Polynomial ℤ :=
  X ^ 2 + X + 1

private def dyadicBezoutQuotient : Polynomial ℤ :=
  -X ^ 16 + 3 * X ^ 15 - 8 * X ^ 13 + 4 * X ^ 12 +
    15 * X ^ 11 - 12 * X ^ 10 - 13 * X ^ 9 + 20 * X ^ 8 +
    3 * X ^ 7 - 15 * X ^ 6 + 6 * X ^ 5 + 5 * X ^ 4 -
    4 * X ^ 3 + 4 * X ^ 2 + 3 * X - 1

private theorem dyadicBezoutPolynomial_identity :
    alphaBezoutPolynomial * alphaPolynomialInt +
        betaBezoutPolynomial * betaPolynomialInt +
      relationBezoutPolynomial * normalizedPolynomialInt =
        1 + 2 * dyadicBezoutQuotient := by
  simp only [alphaBezoutPolynomial, betaBezoutPolynomial,
    relationBezoutPolynomial, dyadicBezoutQuotient,
    alphaPolynomialInt, betaPolynomialInt, normalizedPolynomialInt]
  ring

private theorem alphaInteger_eq_aeval :
    alphaInteger = Polynomial.aeval normalizedInteger alphaPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change alpha =
    (IsScalarTower.toAlgHom ℤ OM M)
      (Polynomial.aeval normalizedInteger alphaPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ OM M) normalizedInteger alphaPolynomialInt]
  simpa only [normalizedInteger_coe, IsScalarTower.toAlgHom_apply] using
    alpha_formula

private theorem betaInteger_eq_aeval :
    betaInteger = Polynomial.aeval normalizedInteger betaPolynomialInt := by
  apply RingOfIntegers.coe_injective
  change beta =
    (IsScalarTower.toAlgHom ℤ OM M)
      (Polynomial.aeval normalizedInteger betaPolynomialInt)
  rw [← Polynomial.aeval_algHom_apply
    (IsScalarTower.toAlgHom ℤ OM M) normalizedInteger betaPolynomialInt]
  simpa only [normalizedInteger_coe, IsScalarTower.toAlgHom_apply] using
    beta_formula

private theorem dyadicBezout_evaluated :
    Polynomial.aeval normalizedInteger alphaBezoutPolynomial * alphaInteger +
        Polynomial.aeval normalizedInteger betaBezoutPolynomial * betaInteger =
      1 + 2 * Polynomial.aeval normalizedInteger dyadicBezoutQuotient := by
  rw [alphaInteger_eq_aeval, betaInteger_eq_aeval, ← map_mul, ← map_mul]
  have h := congrArg (Polynomial.aeval normalizedInteger)
    dyadicBezoutPolynomial_identity
  simp only [map_add, map_mul, map_one, map_ofNat,
    normalizedInteger_aeval, mul_zero, add_zero] at h
  simpa only [map_mul] using h

private theorem two_mem_alphaIdeal : (2 : OM) ∈ alphaIdeal := by
  rw [← Ideal.span_singleton_le_iff_mem]
  rw [span_two_eq_span_alpha_mul_span_beta_sq]
  exact (Ideal.mul_le_left : alphaIdeal * betaIdeal ^ 2 ≤ alphaIdeal)

private theorem two_mem_betaIdeal : (2 : OM) ∈ betaIdeal := by
  rw [← Ideal.span_singleton_le_iff_mem]
  rw [span_two_eq_span_alpha_mul_span_beta_sq]
  exact (Ideal.mul_le_right : alphaIdeal * betaIdeal ^ 2 ≤ betaIdeal ^ 2).trans
    (Ideal.pow_le_self (show (2 : ℕ) ≠ 0 by decide))

private theorem alphaIdeal_ne_betaIdeal : alphaIdeal ≠ betaIdeal := by
  intro hEq
  have hAlpha : alphaInteger ∈ alphaIdeal :=
    Ideal.subset_span (Set.mem_singleton alphaInteger)
  have hBeta : betaInteger ∈ alphaIdeal := by
    rw [hEq]
    exact Ideal.subset_span (Set.mem_singleton betaInteger)
  have hLeft :
      Polynomial.aeval normalizedInteger alphaBezoutPolynomial * alphaInteger +
          Polynomial.aeval normalizedInteger betaBezoutPolynomial * betaInteger ∈
        alphaIdeal :=
    alphaIdeal.add_mem
      (alphaIdeal.mul_mem_left _ hAlpha) (alphaIdeal.mul_mem_left _ hBeta)
  have hTwoMultiple :
      2 * Polynomial.aeval normalizedInteger dyadicBezoutQuotient ∈
        alphaIdeal := alphaIdeal.mul_mem_right _ two_mem_alphaIdeal
  have hOne : (1 : OM) ∈ alphaIdeal := by
    rw [dyadicBezout_evaluated] at hLeft
    have hsub := alphaIdeal.sub_mem hLeft hTwoMultiple
    convert hsub using 1
    ring
  have hTop : alphaIdeal = ⊤ := (Ideal.eq_top_iff_one alphaIdeal).mpr hOne
  have hNorm := absNorm_span_alpha
  change Ideal.absNorm alphaIdeal = 8 at hNorm
  rw [hTop, Ideal.absNorm_top] at hNorm
  norm_num at hNorm

private theorem eq_of_dvd_of_absNorm_eq
    {I J : Ideal OM} (hdiv : I ∣ J)
    (hI : I.absNorm = 8) (hJ : J.absNorm = 8) : I = J := by
  obtain ⟨C, hC⟩ := hdiv
  have hnorm := congrArg Ideal.absNorm hC
  rw [map_mul, hI, hJ] at hnorm
  have hCnorm : C.absNorm = 1 := by omega
  have hCtop : C = ⊤ := Ideal.absNorm_eq_one_iff.mp hCnorm
  rw [hCtop, mul_top] at hC
  exact hC.symm

private theorem alphaIdeal_ne_bot : alphaIdeal ≠ ⊥ := by
  intro hbot
  have hnorm := absNorm_span_alpha
  change Ideal.absNorm alphaIdeal = 8 at hnorm
  rw [hbot, Ideal.absNorm_bot] at hnorm
  norm_num at hnorm

private theorem betaIdeal_ne_bot : betaIdeal ≠ ⊥ := by
  intro hbot
  have hnorm := absNorm_span_beta
  change Ideal.absNorm betaIdeal = 8 at hnorm
  rw [hbot, Ideal.absNorm_bot] at hnorm
  norm_num at hnorm

private theorem alphaIdeal_not_isUnit : ¬ IsUnit alphaIdeal := by
  intro hunit
  have htop : alphaIdeal = ⊤ := Ideal.isUnit_iff.mp hunit
  have hnorm := absNorm_span_alpha
  change Ideal.absNorm alphaIdeal = 8 at hnorm
  rw [htop, Ideal.absNorm_top] at hnorm
  norm_num at hnorm

private theorem betaIdeal_not_isUnit : ¬ IsUnit betaIdeal := by
  intro hunit
  have htop : betaIdeal = ⊤ := Ideal.isUnit_iff.mp hunit
  have hnorm := absNorm_span_beta
  change Ideal.absNorm betaIdeal = 8 at hnorm
  rw [htop, Ideal.absNorm_top] at hnorm
  norm_num at hnorm

private theorem primeFactor_mem_primesOver_two
    {P I : Ideal OM} (hP : P.IsPrime) (hPdivI : P ∣ I)
    (hIdivTwo : I ∣ Ideal.span {(2 : OM)}) :
    P ∈ Ideal.primesOver (Ideal.span {(2 : ℤ)}) OM := by
  letI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
    Int.ideal_span_isMaximal_of_prime 2
  refine ⟨hP, ?_⟩
  apply (Ideal.liesOver_iff_dvd_map hP.ne_top).mpr
  have hPdivTwo : P ∣ Ideal.span {(2 : OM)} := hPdivI.trans hIdivTwo
  simpa only [Ideal.map_span, Set.image_singleton, map_ofNat] using hPdivTwo

private theorem alphaIdeal_isPrime : alphaIdeal.IsPrime := by
  obtain ⟨P, hPirr, hPdiv⟩ :=
    WfDvdMonoid.exists_irreducible_factor alphaIdeal_not_isUnit
      alphaIdeal_ne_bot
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hPirr)
  have hAlphaDivTwo : alphaIdeal ∣ Ideal.span {(2 : OM)} :=
    ⟨betaIdeal ^ 2, span_two_eq_span_alpha_mul_span_beta_sq⟩
  have hPover := primeFactor_mem_primesOver_two hPprime hPdiv hAlphaDivTwo
  rcases prime_over_two_eq_span_alpha_or_beta P hPover with hEq | hEq
  · simpa only [hEq] using hPprime
  · have hBetaDivAlpha : betaIdeal ∣ alphaIdeal := by simpa only [hEq] using hPdiv
    have hBetaAlpha : betaIdeal = alphaIdeal :=
      eq_of_dvd_of_absNorm_eq hBetaDivAlpha absNorm_span_beta absNorm_span_alpha
    exact False.elim (alphaIdeal_ne_betaIdeal hBetaAlpha.symm)

private theorem betaIdeal_isPrime : betaIdeal.IsPrime := by
  obtain ⟨P, hPirr, hPdiv⟩ :=
    WfDvdMonoid.exists_irreducible_factor betaIdeal_not_isUnit
      betaIdeal_ne_bot
  have hPprime : P.IsPrime := Ideal.isPrime_of_prime
    (UniqueFactorizationMonoid.irreducible_iff_prime.mp hPirr)
  have hBetaDivTwo : betaIdeal ∣ Ideal.span {(2 : OM)} := by
    refine ⟨alphaIdeal * betaIdeal, ?_⟩
    simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
      span_two_eq_span_alpha_mul_span_beta_sq
  have hPover := primeFactor_mem_primesOver_two hPprime hPdiv hBetaDivTwo
  rcases prime_over_two_eq_span_alpha_or_beta P hPover with hEq | hEq
  · have hAlphaDivBeta : alphaIdeal ∣ betaIdeal := by simpa only [hEq] using hPdiv
    have hAlphaBeta : alphaIdeal = betaIdeal :=
      eq_of_dvd_of_absNorm_eq hAlphaDivBeta absNorm_span_alpha absNorm_span_beta
    exact False.elim (alphaIdeal_ne_betaIdeal hAlphaBeta)
  · simpa only [hEq] using hPprime

/-! ## Transport to the relative integral closure -/

private def absoluteAlphaPrime : HeightOneSpectrum OM where
  asIdeal := alphaIdeal
  isPrime := alphaIdeal_isPrime
  ne_bot := alphaIdeal_ne_bot

private def absoluteBetaPrime : HeightOneSpectrum OM where
  asIdeal := betaIdeal
  isPrime := betaIdeal_isPrime
  ne_bot := betaIdeal_ne_bot

private def relativeAbsolutePlaceEquiv :
    HeightOneSpectrum RelativeIntegers ≃ HeightOneSpectrum OM :=
  HeightOneSpectrum.equivOfRingEquiv relativeIntegersEquiv

private def relativeAlphaPrime : HeightOneSpectrum RelativeIntegers :=
  relativeAbsolutePlaceEquiv.symm absoluteAlphaPrime

private def relativeBetaPrime : HeightOneSpectrum RelativeIntegers :=
  relativeAbsolutePlaceEquiv.symm absoluteBetaPrime

private theorem relativeAlphaPrime_ne_relativeBetaPrime :
    relativeAlphaPrime ≠ relativeBetaPrime := by
  intro h
  have habs : absoluteAlphaPrime = absoluteBetaPrime := by
    simpa [relativeAlphaPrime, relativeBetaPrime] using
      congrArg relativeAbsolutePlaceEquiv h
  exact alphaIdeal_ne_betaIdeal (HeightOneSpectrum.ext_iff.mp habs)

private def relativeAlphaInteger : RelativeIntegers :=
  relativeIntegersEquiv.symm alphaInteger

private def relativeBetaInteger : RelativeIntegers :=
  relativeIntegersEquiv.symm betaInteger

@[simp] private theorem relativeIntegersEquiv_relativeAlphaInteger :
    relativeIntegersEquiv relativeAlphaInteger = alphaInteger := by
  simp [relativeAlphaInteger]

@[simp] private theorem relativeIntegersEquiv_relativeBetaInteger :
    relativeIntegersEquiv relativeBetaInteger = betaInteger := by
  simp [relativeBetaInteger]

private theorem relativeAlphaPrime_span :
    relativeAlphaPrime.asIdeal = Ideal.span {relativeAlphaInteger} := by
  have hmap :
      (Ideal.span {relativeAlphaInteger}).map
          relativeIntegersEquiv.toRingHom = alphaIdeal := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {relativeIntegersEquiv relativeAlphaInteger} = alphaIdeal
    rw [relativeIntegersEquiv_relativeAlphaInteger]
  change alphaIdeal.comap relativeIntegersEquiv.toRingHom =
    Ideal.span {relativeAlphaInteger}
  rw [← hmap]
  exact Ideal.comap_map_of_bijective
    relativeIntegersEquiv.toRingHom relativeIntegersEquiv.bijective

private theorem relativeBetaPrime_span :
    relativeBetaPrime.asIdeal = Ideal.span {relativeBetaInteger} := by
  have hmap :
      (Ideal.span {relativeBetaInteger}).map
          relativeIntegersEquiv.toRingHom = betaIdeal := by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {relativeIntegersEquiv relativeBetaInteger} = betaIdeal
    rw [relativeIntegersEquiv_relativeBetaInteger]
  change betaIdeal.comap relativeIntegersEquiv.toRingHom =
    Ideal.span {relativeBetaInteger}
  rw [← hmap]
  exact Ideal.comap_map_of_bijective
    relativeIntegersEquiv.toRingHom relativeIntegersEquiv.bijective

private theorem relativeAlphaInteger_coe :
    algebraMap RelativeIntegers M relativeAlphaInteger = alpha := by
  have h := IsIntegralClosure.algebraMap_equiv
    (𝓞 K) RelativeIntegers M (𝓞 M) relativeAlphaInteger
  simpa [relativeIntegersEquiv, relativeAlphaInteger] using h.symm

private theorem relativeBetaInteger_coe :
    algebraMap RelativeIntegers M relativeBetaInteger = beta := by
  have h := IsIntegralClosure.algebraMap_equiv
    (𝓞 K) RelativeIntegers M (𝓞 M) relativeBetaInteger
  simpa [relativeIntegersEquiv, relativeBetaInteger] using h.symm

private theorem relativeIntegersEquiv_algebraMap (x : 𝓞 K) :
    relativeIntegersEquiv
        (algebraMap (𝓞 K) RelativeIntegers x) =
      algebraMap (𝓞 K) (𝓞 M) x := by
  apply RingOfIntegers.coe_injective
  calc
    algebraMap (𝓞 M) M
        (relativeIntegersEquiv
          (algebraMap (𝓞 K) RelativeIntegers x)) =
        algebraMap RelativeIntegers M
          (algebraMap (𝓞 K) RelativeIntegers x) := by
      exact IsIntegralClosure.algebraMap_equiv
        (𝓞 K) RelativeIntegers M (𝓞 M)
          (algebraMap (𝓞 K) RelativeIntegers x)
    _ = algebraMap (𝓞 K) M x :=
      IsScalarTower.algebraMap_apply (𝓞 K) RelativeIntegers M x
    _ = algebraMap (𝓞 M) M
        (algebraMap (𝓞 K) (𝓞 M) x) := by
      rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 M) M]

private theorem relativeAlphaPrime_below :
    relativeAlphaPrime.below (𝓞 K) = coefficientPrimeTwo := by
  apply HeightOneSpectrum.ext
  symm
  apply coefficientPrimeTwo.isMaximal.eq_of_le
    (relativeAlphaPrime.below (𝓞 K)).isPrime.ne_top
  rw [coefficientPrimeTwo_span, Ideal.span_singleton_le_iff_mem]
  change relativeIntegersEquiv
      (algebraMap (𝓞 K) RelativeIntegers 2) ∈ alphaIdeal
  rw [relativeIntegersEquiv_algebraMap]
  exact two_mem_alphaIdeal

private theorem relativeBetaPrime_below :
    relativeBetaPrime.below (𝓞 K) = coefficientPrimeTwo := by
  apply HeightOneSpectrum.ext
  symm
  apply coefficientPrimeTwo.isMaximal.eq_of_le
    (relativeBetaPrime.below (𝓞 K)).isPrime.ne_top
  rw [coefficientPrimeTwo_span, Ideal.span_singleton_le_iff_mem]
  change relativeIntegersEquiv
      (algebraMap (𝓞 K) RelativeIntegers 2) ∈ betaIdeal
  rw [relativeIntegersEquiv_algebraMap]
  exact two_mem_betaIdeal

private theorem relativeAlphaPrime_mem :
    relativeAlphaPrime ∈ compositumDyadicSupport := by
  rw [compositumDyadicSupport,
    HeightOneSpectrum.mem_primesAbove_iff,
    coefficientDyadicSupport_eq_singleton,
    Set.mem_singleton_iff]
  exact relativeAlphaPrime_below

private theorem relativeBetaPrime_mem :
    relativeBetaPrime ∈ compositumDyadicSupport := by
  rw [compositumDyadicSupport,
    HeightOneSpectrum.mem_primesAbove_iff,
    coefficientDyadicSupport_eq_singleton,
    Set.mem_singleton_iff]
  exact relativeBetaPrime_below

private theorem relative_prime_eq_alpha_or_beta
    (w : HeightOneSpectrum RelativeIntegers)
    (hw : w ∈ compositumDyadicSupport) :
    w = relativeAlphaPrime ∨ w = relativeBetaPrime := by
  have hwBelow : w.below (𝓞 K) = coefficientPrimeTwo := by
    rw [compositumDyadicSupport,
      HeightOneSpectrum.mem_primesAbove_iff,
      coefficientDyadicSupport_eq_singleton,
      Set.mem_singleton_iff] at hw
    exact hw
  let P : HeightOneSpectrum OM := relativeAbsolutePlaceEquiv w
  have htwoRelative :
      algebraMap (𝓞 K) RelativeIntegers (2 : 𝓞 K) ∈ w.asIdeal := by
    change (2 : 𝓞 K) ∈ (w.below (𝓞 K)).asIdeal
    rw [hwBelow, coefficientPrimeTwo_span]
    exact Ideal.subset_span (Set.mem_singleton (2 : 𝓞 K))
  have htwoAbsolute : (2 : OM) ∈ P.asIdeal := by
    change relativeIntegersEquiv.symm (2 : OM) ∈ w.asIdeal
    have hmap := relativeIntegersEquiv_algebraMap (2 : 𝓞 K)
    have hsymm :
        relativeIntegersEquiv.symm (2 : OM) =
          algebraMap (𝓞 K) RelativeIntegers (2 : 𝓞 K) := by
      apply relativeIntegersEquiv.injective
      exact (relativeIntegersEquiv.apply_symm_apply (2 : OM)).trans hmap.symm
    rw [hsymm]
    exact htwoRelative
  have hPover : P.asIdeal ∈
      Ideal.primesOver (Ideal.span {(2 : ℤ)}) OM := by
    letI : (Ideal.span {(2 : ℤ)}).IsMaximal :=
      Int.ideal_span_isMaximal_of_prime 2
    refine ⟨P.isPrime, ?_⟩
    apply (Ideal.liesOver_iff_dvd_map P.isPrime.ne_top).mpr
    rw [Ideal.map_span, Set.image_singleton, map_ofNat, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem]
    exact htwoAbsolute
  rcases prime_over_two_eq_span_alpha_or_beta P.asIdeal hPover with hP | hP
  · left
    apply relativeAbsolutePlaceEquiv.injective
    apply HeightOneSpectrum.ext
    simpa only [relativeAlphaPrime, Equiv.apply_symm_apply,
      absoluteAlphaPrime] using hP
  · right
    apply relativeAbsolutePlaceEquiv.injective
    apply HeightOneSpectrum.ext
    simpa only [relativeBetaPrime, Equiv.apply_symm_apply,
      absoluteBetaPrime] using hP

/-! ## The exact two-place indexing -/

private def dyadicPlaceMap : Fin 2 → compositumDyadicSupport
  | 0 => ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩
  | 1 => ⟨relativeBetaPrime, relativeBetaPrime_mem⟩

private theorem dyadicPlaceMap_injective :
    Function.Injective dyadicPlaceMap := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim (relativeAlphaPrime_ne_relativeBetaPrime
      (congrArg Subtype.val hij))
  · exact False.elim (relativeAlphaPrime_ne_relativeBetaPrime
      (congrArg Subtype.val hij).symm)
  · rfl

private theorem dyadicPlaceMap_surjective :
    Function.Surjective dyadicPlaceMap := by
  intro w
  rcases relative_prime_eq_alpha_or_beta w w.property with hw | hw
  · refine ⟨0, ?_⟩
    apply Subtype.ext
    exact hw.symm
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    exact hw.symm

private def dyadicPlaceEquiv : Fin 2 ≃ compositumDyadicSupport :=
  Equiv.ofBijective dyadicPlaceMap
    ⟨dyadicPlaceMap_injective, dyadicPlaceMap_surjective⟩

/-! ## The valuation-parity matrix -/

private theorem alpha_ne_zero : alpha ≠ 0 := by
  intro hz
  have h := norm_alpha
  rw [hz, Algebra.norm_zero] at h
  norm_num at h

private theorem beta_ne_zero : beta ≠ 0 := by
  intro hz
  have h := norm_beta
  rw [hz, Algebra.norm_zero] at h
  have htau : Q.tau + 1 ≠ 0 := by
    have ht :=
      MazurTorsion.XOneEighteenRealCubicQuotient.rational_add_tau_ne_zero
        (1 : ℚ)
    change (1 : K) + Q.tau ≠ 0 at ht
    simpa only [add_comm] using ht
  apply htau
  linear_combination (-1 / 2) * h

private theorem relativeAlphaInteger_ne_zero : relativeAlphaInteger ≠ 0 := by
  intro hz
  have h := congrArg (algebraMap RelativeIntegers M) hz
  rw [relativeAlphaInteger_coe, map_zero] at h
  exact alpha_ne_zero h

private theorem relativeBetaInteger_ne_zero : relativeBetaInteger ≠ 0 := by
  intro hz
  have h := congrArg (algebraMap RelativeIntegers M) hz
  rw [relativeBetaInteger_coe, map_zero] at h
  exact beta_ne_zero h

private theorem relativeAlphaInteger_not_mem_betaPrime :
    relativeAlphaInteger ∉ relativeBetaPrime.asIdeal := by
  intro hmem
  have hle : relativeAlphaPrime.asIdeal ≤ relativeBetaPrime.asIdeal := by
    rw [relativeAlphaPrime_span, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hideals :
      relativeAlphaPrime.asIdeal = relativeBetaPrime.asIdeal :=
    relativeAlphaPrime.isMaximal.eq_of_le
      relativeBetaPrime.isPrime.ne_top hle
  exact relativeAlphaPrime_ne_relativeBetaPrime
    (HeightOneSpectrum.ext hideals)

private theorem relativeBetaInteger_not_mem_alphaPrime :
    relativeBetaInteger ∉ relativeAlphaPrime.asIdeal := by
  intro hmem
  have hle : relativeBetaPrime.asIdeal ≤ relativeAlphaPrime.asIdeal := by
    rw [relativeBetaPrime_span, Ideal.span_singleton_le_iff_mem]
    exact hmem
  have hideals :
      relativeBetaPrime.asIdeal = relativeAlphaPrime.asIdeal :=
    relativeBetaPrime.isMaximal.eq_of_le
      relativeAlphaPrime.isPrime.ne_top hle
  exact relativeAlphaPrime_ne_relativeBetaPrime
    (HeightOneSpectrum.ext hideals).symm

private theorem alphaSquareclass_mem : alphaSquareclass ∈ DyadicSelmerM := by
  intro w hw
  rw [alphaSquareclass, fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
  have hwne : w ≠ relativeAlphaPrime := by
    intro heq
    apply hw
    simpa only [heq] using relativeAlphaPrime_mem
  have hnotmem : relativeAlphaInteger ∉ w.asIdeal := by
    intro hmem
    have hle : relativeAlphaPrime.asIdeal ≤ w.asIdeal := by
      rw [relativeAlphaPrime_span, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have hideals : relativeAlphaPrime.asIdeal = w.asIdeal :=
      relativeAlphaPrime.isMaximal.eq_of_le w.isPrime.ne_top hle
    exact hwne (HeightOneSpectrum.ext hideals.symm)
  have hval : w.valuation M alpha = 1 := by
    rw [← relativeAlphaInteger_coe]
    exact w.valuation_eq_one_iff_notMem.mpr hnotmem
  have hvalUnit :
      w.valuationOfNeZero (Units.mk0 alpha alpha_ne_zero) = 1 := by
    rw [w.valuationOfNeZero_eq_iff]
    simpa only [Units.val_mk0, WithZero.coe_one] using hval
  rw [hvalUnit]
  simp

private theorem betaSquareclass_mem : betaSquareclass ∈ DyadicSelmerM := by
  intro w hw
  rw [betaSquareclass, fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff]
  have hwne : w ≠ relativeBetaPrime := by
    intro heq
    apply hw
    simpa only [heq] using relativeBetaPrime_mem
  have hnotmem : relativeBetaInteger ∉ w.asIdeal := by
    intro hmem
    have hle : relativeBetaPrime.asIdeal ≤ w.asIdeal := by
      rw [relativeBetaPrime_span, Ideal.span_singleton_le_iff_mem]
      exact hmem
    have hideals : relativeBetaPrime.asIdeal = w.asIdeal :=
      relativeBetaPrime.isMaximal.eq_of_le w.isPrime.ne_top hle
    exact hwne (HeightOneSpectrum.ext hideals.symm)
  have hval : w.valuation M beta = 1 := by
    rw [← relativeBetaInteger_coe]
    exact w.valuation_eq_one_iff_notMem.mpr hnotmem
  have hvalUnit :
      w.valuationOfNeZero (Units.mk0 beta beta_ne_zero) = 1 := by
    rw [w.valuationOfNeZero_eq_iff]
    simpa only [Units.val_mk0, WithZero.coe_one] using hval
  rw [hvalUnit]
  simp

private def supportedAlpha : DyadicSelmerM :=
  ⟨alphaSquareclass, alphaSquareclass_mem⟩

private def supportedBeta : DyadicSelmerM :=
  ⟨betaSquareclass, betaSquareclass_mem⟩

private theorem relativeAlphaPrime_valuation_alpha :
    relativeAlphaPrime.valuation M alpha = WithZero.exp (-1 : ℤ) := by
  calc
    relativeAlphaPrime.valuation M alpha =
        relativeAlphaPrime.valuation M
          (algebraMap RelativeIntegers M relativeAlphaInteger) := by
      rw [relativeAlphaInteger_coe]
    _ = relativeAlphaPrime.intValuation relativeAlphaInteger := by
      exact relativeAlphaPrime.valuation_of_algebraMap
        (K := M) relativeAlphaInteger
    _ = WithZero.exp (-1 : ℤ) :=
      relativeAlphaPrime.intValuation_singleton
        relativeAlphaInteger_ne_zero relativeAlphaPrime_span

private theorem relativeBetaPrime_valuation_beta :
    relativeBetaPrime.valuation M beta = WithZero.exp (-1 : ℤ) := by
  calc
    relativeBetaPrime.valuation M beta =
        relativeBetaPrime.valuation M
          (algebraMap RelativeIntegers M relativeBetaInteger) := by
      rw [relativeBetaInteger_coe]
    _ = relativeBetaPrime.intValuation relativeBetaInteger := by
      exact relativeBetaPrime.valuation_of_algebraMap
        (K := M) relativeBetaInteger
    _ = WithZero.exp (-1 : ℤ) :=
      relativeBetaPrime.intValuation_singleton
        relativeBetaInteger_ne_zero relativeBetaPrime_span

private theorem relativeAlphaPrime_valuation_beta :
    relativeAlphaPrime.valuation M beta = 1 := by
  rw [← relativeBetaInteger_coe]
  exact relativeAlphaPrime.valuation_eq_one_iff_notMem.mpr
    relativeBetaInteger_not_mem_alphaPrime

private theorem relativeBetaPrime_valuation_alpha :
    relativeBetaPrime.valuation M alpha = 1 := by
  rw [← relativeAlphaInteger_coe]
  exact relativeBetaPrime.valuation_eq_one_iff_notMem.mpr
    relativeAlphaInteger_not_mem_betaPrime

private theorem relativeAlphaPrime_valuationOfNeZero_alpha :
    relativeAlphaPrime.valuationOfNeZero
        (Units.mk0 alpha alpha_ne_zero) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  rw [relativeAlphaPrime.valuationOfNeZero_eq_iff]
  change relativeAlphaPrime.valuation M alpha = WithZero.exp (-1 : ℤ)
  exact relativeAlphaPrime_valuation_alpha

private theorem relativeBetaPrime_valuationOfNeZero_beta :
    relativeBetaPrime.valuationOfNeZero
        (Units.mk0 beta beta_ne_zero) =
      Multiplicative.ofAdd (-1 : ℤ) := by
  rw [relativeBetaPrime.valuationOfNeZero_eq_iff]
  change relativeBetaPrime.valuation M beta = WithZero.exp (-1 : ℤ)
  exact relativeBetaPrime_valuation_beta

private theorem relativeAlphaPrime_valuationOfNeZero_beta :
    relativeAlphaPrime.valuationOfNeZero
        (Units.mk0 beta beta_ne_zero) = 1 := by
  rw [relativeAlphaPrime.valuationOfNeZero_eq_iff]
  simpa only [Units.val_mk0, WithZero.coe_one] using
    relativeAlphaPrime_valuation_beta

private theorem relativeBetaPrime_valuationOfNeZero_alpha :
    relativeBetaPrime.valuationOfNeZero
        (Units.mk0 alpha alpha_ne_zero) = 1 := by
  rw [relativeBetaPrime.valuationOfNeZero_eq_iff]
  simpa only [Units.val_mk0, WithZero.coe_one] using
    relativeBetaPrime_valuation_alpha

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

private theorem supportedAlpha_at_alpha_ne_one :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedAlpha
          ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ ≠ 1 := by
  intro hone
  have hdvd : (2 : ℤ) ∣ Multiplicative.toAdd
      (relativeAlphaPrime.valuationOfNeZero
        (Units.mk0 alpha alpha_ne_zero)) := by
    apply (HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
      relativeAlphaPrime 2 (Units.mk0 alpha alpha_ne_zero)).mp
    exact hone
  rw [relativeAlphaPrime_valuationOfNeZero_alpha] at hdvd
  norm_num at hdvd

private theorem supportedBeta_at_beta_ne_one :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedBeta
          ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ ≠ 1 := by
  intro hone
  have hdvd : (2 : ℤ) ∣ Multiplicative.toAdd
      (relativeBetaPrime.valuationOfNeZero
        (Units.mk0 beta beta_ne_zero)) := by
    apply (HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff
      relativeBetaPrime 2 (Units.mk0 beta beta_ne_zero)).mp
    exact hone
  rw [relativeBetaPrime_valuationOfNeZero_beta] at hdvd
  norm_num at hdvd

private theorem supportedAlpha_at_alpha :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedAlpha
          ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ = parityOne := by
  rcases eq_one_or_parityOne
    (supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedAlpha
        ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩) with h | h
  · exact False.elim (supportedAlpha_at_alpha_ne_one h)
  · exact h

private theorem supportedBeta_at_beta :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedBeta
          ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ = parityOne := by
  rcases eq_one_or_parityOne
    (supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedBeta
        ⟨relativeBetaPrime, relativeBetaPrime_mem⟩) with h | h
  · exact False.elim (supportedBeta_at_beta_ne_one h)
  · exact h

private theorem supportedAlpha_at_beta :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedAlpha
          ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ = 1 := by
  change relativeBetaPrime.valuationOfNeZeroMod 2 alphaSquareclass = 1
  rw [alphaSquareclass, fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff,
    relativeBetaPrime_valuationOfNeZero_alpha]
  simp

private theorem supportedBeta_at_alpha :
    supportValuation (R := RelativeIntegers) (K := M)
        compositumDyadicSupport 2 supportedBeta
          ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ = 1 := by
  change relativeAlphaPrime.valuationOfNeZeroMod 2 betaSquareclass = 1
  rw [betaSquareclass, fieldSquareclass,
    HeightOneSpectrum.valuationOfNeZeroMod_mk_eq_one_iff,
    relativeAlphaPrime_valuationOfNeZero_beta]
  simp

/-- The exact two-prime valuation certificate for the degree-nine dyadic
supported squareclass group. -/
def dyadicValuationCertificate : DyadicValuationCertificate where
  places := dyadicPlaceEquiv
  alpha_mem := alphaSquareclass_mem
  beta_mem := betaSquareclass_mem
  alpha_at_zero := by
    change supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedAlpha
        ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ = parityOne
    exact supportedAlpha_at_alpha
  alpha_at_one := by
    change supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedAlpha
        ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ = 1
    exact supportedAlpha_at_beta
  beta_at_zero := by
    change supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedBeta
        ⟨relativeAlphaPrime, relativeAlphaPrime_mem⟩ = 1
    exact supportedBeta_at_alpha
  beta_at_one := by
    change supportValuation (R := RelativeIntegers) (K := M)
      compositumDyadicSupport 2 supportedBeta
        ⟨relativeBetaPrime, relativeBetaPrime_mem⟩ = parityOne
    exact supportedBeta_at_beta

end


end MazurTorsion.XOneEighteenDyadicValuationCertificate

end

theorem solution :
Nonempty MazurTorsion.XOneEighteenGlobalSelmerBridge.DyadicValuationCertificate := by
  exact ⟨MazurTorsion.XOneEighteenDyadicValuationCertificate.dyadicValuationCertificate⟩

#print axioms solution
