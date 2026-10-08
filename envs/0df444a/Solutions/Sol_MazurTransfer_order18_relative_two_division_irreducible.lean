-- Prove2me | solution 1 for MazurTransfer.order18_relative_two_division_irreducible
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T17:48:15.219989+00:00
-- url     : https://prove2.me/submissions/212e0121-ea71-4a4c-9598-01dfe2cb1a0c

import Mathlib
import Definitions.Def_MazurTransfer_Order18RelativeAlgebra
import Theorems.Thm_MazurTransfer_order18_rational_cubics_irreducible

noncomputable section


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







/-- The dimension of `K[X]/(f)` over `K` is the degree of `f`. -/
theorem finrank_eq_natDegree (hf : f ≠ 0) : Module.finrank K (AdjoinRoot f) = f.natDegree := by
  rw [(powerBasis hf).finrank, powerBasis_dim]



























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

















/-- Irreducibility of `S³ - 3S - 10` over `ℚ`. -/
theorem twoDivisionPolynomial_irreducible :
    Irreducible twoDivisionPolynomial := by
  exact MazurTransfer.order18_rational_cubics_irreducible.2




theorem twoDivisionPolynomial_natDegree :
    twoDivisionPolynomial.natDegree = 3 := by
  simp only [twoDivisionPolynomial]
  compute_degree!







/-- The defining relation for `sigma`. -/
theorem sigma_cubic : sigma ^ 3 = 3 * sigma + 10 := by
  have h : AdjoinRoot.mk twoDivisionPolynomial twoDivisionPolynomial = 0 :=
    AdjoinRoot.mk_self
  change AdjoinRoot.mk twoDivisionPolynomial
    (X ^ 3 - 3 * X - 10 : Polynomial ℚ) = 0 at h
  rw [map_sub, map_sub, map_pow, map_mul, map_ofNat, map_ofNat,
    AdjoinRoot.mk_X] at h
  have h' : sigma ^ 3 - 3 * sigma - 10 = 0 := by
    simpa only [sigma] using h
  linear_combination h'

/-- The rational cubic field has degree `3`. -/
theorem finrank_F_over_rat : Module.finrank ℚ F = 3 := by
  rw [AdjoinRoot.finrank_eq_natDegree
    (twoDivisionPolynomial_irreducible.ne_zero),
    twoDivisionPolynomial_natDegree]







/-! ## The relative cubic algebra over the quotient field -/





theorem relativePolynomial_natDegree : relativePolynomial.natDegree = 3 := by
  simp only [relativePolynomial]
  compute_degree!



















/-! ## Exact relative norm certificates -/

























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

private theorem twoDivisionPolynomial_monic : twoDivisionPolynomial.Monic := by
  simp only [twoDivisionPolynomial]
  monicity <;> norm_num

private def twoDivisionPowerBasis : PowerBasis ℚ F :=
  AdjoinRoot.powerBasis' twoDivisionPolynomial_monic

private theorem coefficientPowerBasis_minpolyGen :
    coefficientPowerBasis.minpolyGen = Q.cubicPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval Q.tau Q.cubicPolynomial = 0 := by
    simp only [Q.cubicPolynomial,
      MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
      map_sub, map_pow, aeval_X, map_mul, map_ofNat, map_one]
    linear_combination Q.tau_cubic
  exact (minpoly.eq_of_irreducible_of_monic Q.cubicPolynomial_irreducible
    hroot coefficientPolynomial_monic).symm

private theorem twoDivisionPowerBasis_minpolyGen :
    twoDivisionPowerBasis.minpolyGen = twoDivisionPolynomial := by
  rw [PowerBasis.minpolyGen_eq]
  have hroot : Polynomial.aeval sigma twoDivisionPolynomial = 0 := by
    simp only [twoDivisionPolynomial, map_sub, map_pow, aeval_X,
      map_mul, map_ofNat]
    linear_combination sigma_cubic
  exact (minpoly.eq_of_irreducible_of_monic twoDivisionPolynomial_irreducible
    hroot twoDivisionPolynomial_monic).symm

private theorem coefficientPowerBasis_dim : coefficientPowerBasis.dim = 3 := by
  rw [coefficientPowerBasis, AdjoinRoot.powerBasis'_dim]
  simp only [MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial]
  compute_degree!

private theorem twoDivisionPowerBasis_dim : twoDivisionPowerBasis.dim = 3 := by
  rw [twoDivisionPowerBasis, AdjoinRoot.powerBasis'_dim]
  exact twoDivisionPolynomial_natDegree

/-! ## The two incompatible cubic discriminants -/

/-- Determinant certificate for the derivative norm of a depressed cubic
`X³ - 3X - d`.  This is deliberately proved at the level of an arbitrary
power basis, so the certificate does not depend on an external polynomial
discriminant computation. -/
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

private theorem coefficientPowerBasis_discriminant :
    Algebra.discr ℚ coefficientPowerBasis.basis = 81 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [coefficientPowerBasis.finrank, coefficientPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, coefficientPowerBasis_minpolyGen]
  simp only [Q.cubicPolynomial,
    MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
    derivative_sub, derivative_pow, derivative_X, derivative_mul,
    derivative_ofNat, derivative_one, mul_one, Nat.cast_ofNat,
    zero_mul, sub_zero]
  rw [show coefficientPowerBasis.gen = Q.tau by rfl]
  have hnorm := norm_cubic_derivative coefficientPowerBasis
    coefficientPowerBasis_dim 1 (by
      simpa only [Q.cubicPolynomial,
        MazurTorsion.XOneEighteenRealCubicQuotient.cubicPolynomial,
        C_1] using coefficientPowerBasis_minpolyGen)
  rw [show coefficientPowerBasis.gen = Q.tau by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]
  norm_num

private theorem twoDivisionPowerBasis_discriminant :
    Algebra.discr ℚ twoDivisionPowerBasis.basis = -2592 := by
  rw [Algebra.discr_powerBasis_eq_norm]
  rw [twoDivisionPowerBasis.finrank, twoDivisionPowerBasis_dim,
    ← PowerBasis.minpolyGen_eq, twoDivisionPowerBasis_minpolyGen]
  simp only [twoDivisionPolynomial, derivative_sub, derivative_pow,
    derivative_X, derivative_mul, derivative_ofNat, mul_one,
    Nat.cast_ofNat, zero_mul, sub_zero]
  rw [show twoDivisionPowerBasis.gen = sigma by rfl]
  have hnorm := norm_cubic_derivative twoDivisionPowerBasis
    twoDivisionPowerBasis_dim 10 (by
      simpa only [twoDivisionPolynomial, Polynomial.C_ofNat] using
        twoDivisionPowerBasis_minpolyGen)
  rw [show twoDivisionPowerBasis.gen = sigma by rfl] at hnorm
  norm_num at hnorm ⊢
  rw [map_ofNat]
  rw [hnorm]

/-! ## Linear disjointness of the two rational cubic fields -/

private theorem coefficientField_finrank : Module.finrank ℚ Q.K = 3 := by
  rw [coefficientPowerBasis.finrank, coefficientPowerBasis_dim]

private theorem relativePolynomial_eq_map :
    twoDivisionPolynomial.map (algebraMap ℚ Q.K) = relativePolynomial := by
  norm_num [twoDivisionPolynomial, relativePolynomial]

/-- The two-division cubic stays irreducible after extending scalars from
`ℚ` to the real cubic coefficient field.  The proof uses only the two exact
power-basis discriminants above, not the ring of integers of either field. -/
theorem relativePolynomial_irreducible : Irreducible relativePolynomial := by
  refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot ?_ ?_
  · rw [relativePolynomial_natDegree]
    norm_num
  · intro x hx
    have hxroot : Polynomial.aeval x twoDivisionPolynomial = 0 := by
      rw [aeval_def, eval₂_eq_eval_map, relativePolynomial_eq_map]
      exact hx
    have hxroot' :
        Polynomial.aeval x (minpoly ℚ twoDivisionPowerBasis.gen) = 0 := by
      rw [← PowerBasis.minpolyGen_eq,
        twoDivisionPowerBasis_minpolyGen]
      exact hxroot
    let φ : F →ₐ[ℚ] Q.K := twoDivisionPowerBasis.lift x hxroot'
    have hφinj : Function.Injective φ := φ.toRingHom.injective
    have hfinrank : Module.finrank ℚ F = Module.finrank ℚ Q.K := by
      rw [finrank_F_over_rat, coefficientField_finrank]
    have hφsurj : Function.Surjective φ :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
        hfinrank).mp hφinj
    let e : F ≃ₐ[ℚ] Q.K := AlgEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
    let mappedBasis : Basis (Fin twoDivisionPowerBasis.dim) ℚ Q.K :=
      twoDivisionPowerBasis.basis.map e.toLinearEquiv
    have hmapped_discriminant :
        Algebra.discr ℚ mappedBasis = -2592 := by
      rw [← twoDivisionPowerBasis_discriminant]
      calc
        Algebra.discr ℚ mappedBasis = Algebra.discr ℚ
            (e ∘ twoDivisionPowerBasis.basis) := by
          congr 1
        _ = Algebra.discr ℚ twoDivisionPowerBasis.basis :=
          (Algebra.discr_eq_discr_of_algEquiv
            twoDivisionPowerBasis.basis e).symm
    let coefficientBasis' : Basis (Fin twoDivisionPowerBasis.dim) ℚ Q.K :=
      coefficientPowerBasis.basis.reindex
        (coefficientPowerBasis.basis.indexEquiv mappedBasis)
    have hcoefficient_discriminant :
        Algebra.discr ℚ coefficientBasis' = 81 := by
      dsimp [coefficientBasis']
      rw [Basis.coe_reindex,
        Algebra.discr_reindex, coefficientPowerBasis_discriminant]
    have hchange :
        Algebra.discr ℚ mappedBasis =
          (coefficientBasis'.toMatrix mappedBasis).det ^ 2 *
            Algebra.discr ℚ coefficientBasis' := by
      convert! Algebra.discr_of_matrix_vecMul coefficientBasis'
        (coefficientBasis'.toMatrix mappedBasis) using 1
      rw [Basis.toMatrix_map_vecMul]
    rw [hmapped_discriminant, hcoefficient_discriminant] at hchange
    have hsquare :
        0 ≤ (coefficientBasis'.toMatrix mappedBasis).det ^ 2 := sq_nonneg _
    nlinarith







end

end MazurTorsion.XOneEighteenTwoDivisionClassNumber

end

theorem solution :
Irreducible MazurTorsion.XOneEighteenTwoDivisionArithmetic.relativePolynomial := by
  exact MazurTorsion.XOneEighteenTwoDivisionClassNumber.relativePolynomial_irreducible

#print axioms solution
end
