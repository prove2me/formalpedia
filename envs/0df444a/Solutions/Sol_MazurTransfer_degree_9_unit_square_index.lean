-- Prove2me | solution 1 for MazurTransfer.degree_9_unit_square_index
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-06T18:09:35.193002+00:00
-- url     : https://prove2.me/submissions/a3c451de-6e62-4508-97c4-12a344fc7e9d

import Mathlib

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



/-- The group of `n`-th power classes of units of `α`. This is the group underlying the
Selmer groups of `Mathlib.RingTheory.DedekindDomain.SelmerGroup`, where it only exists
as a local notation. -/
abbrev Units.modPow (α : Type*) [CommMonoid α] (n : ℕ) : Type _ :=
  αˣ ⧸ (powMonoidHom n : αˣ →* αˣ).range



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

private theorem unitRank_eq_five
    (hdegree : Module.finrank ℚ L = 9)
    (hreal : nrRealPlaces L = 3) :
    NumberField.Units.rank L = 5 := by
  have hsignature := card_add_two_mul_card_eq_rank L
  have hcomplex : nrComplexPlaces L = 3 := by
    rw [hdegree, hreal] at hsignature
    omega
  rw [NumberField.Units.rank, card_eq_nrRealPlaces_add_nrComplexPlaces,
    hreal, hcomplex]

private theorem unitTorsionOrder_eq_two
    (hdegree : Module.finrank ℚ L = 9) :
    NumberField.Units.torsionOrder L = 2 := by
  apply NumberField.Units.torsionOrder_eq_two_of_odd_finrank
  rw [hdegree]
  norm_num

private theorem natCard_ker_two_units_eq_two
    (hdegree : Module.finrank ℚ L = 9) :
    Nat.card
        (nsmulAddMonoidHom (α := Additive (𝓞 L)ˣ) 2).ker = 2 := by
  have htorsion : NumberField.Units.torsionOrder L = 2 :=
    unitTorsionOrder_eq_two L hdegree
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

/-- A degree-nine number field of signature `(3,3)` has exactly `64`
integral-unit square classes. -/
theorem natCard_unitsModSq_of_degree_nine_of_nrRealPlaces_eq_three
    (hdegree : Module.finrank ℚ L = 9)
    (hreal : nrRealPlaces L = 3) :
    Nat.card (Units.modPow (𝓞 L) 2) = 64 := by
  have hrank : NumberField.Units.rank L = 5 :=
    unitRank_eq_five L hdegree hreal
  letI : Group.FG (𝓞 L)ˣ :=
    Group.fg_iff_monoid_fg.mpr inferInstance
  have hindex := AddSubgroup.index_range_nsmul_of_fg
    (Additive (𝓞 L)ˣ) (by norm_num : (2 : ℕ) ≠ 0)
  rw [NumberField.Units.finrank_eq, hrank,
    natCard_ker_two_units_eq_two L hdegree] at hindex
  change
    (nsmulAddMonoidHom (α := Additive (𝓞 L)ˣ) 2).range.index = 64
  norm_num at hindex ⊢
  exact hindex

/-! ## The totally real cubic coefficient field -/









end

end MazurTorsion.XOneEighteenDescent

end

theorem solution :
∀ (L : Type*) [Field L] [NumberField L],
  Module.finrank ℚ L = 9 →
  NumberField.InfinitePlace.nrRealPlaces L = 3 →
  (nsmulAddMonoidHom (α := Additive (NumberField.RingOfIntegers L)ˣ) 2).range.index = 64 := by
  intro L _ _ hdegree hreal
  exact MazurTorsion.XOneEighteenDescent.natCard_unitsModSq_of_degree_nine_of_nrRealPlaces_eq_three L hdegree hreal

#print axioms solution
end
