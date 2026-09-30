-- Prove2me | solution 1 for NumberField.Chebotarev.sum_inv_mul_vonMangoldtTransform_galoisCharacterWeight_apply
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:53.763992+00:00
-- url     : https://prove2.me/submissions/a3b27005-9f92-4cf5-915b-d94d37e902df

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_GroupTheory_FiniteAbelian_CharacterOrthogonality
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Basic
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_GaloisCharacter_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_RamifiedPrimes
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_RingTheory_DedekindDomain_RamificationLocus
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Complex.TaylorSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Abelianization.Defs
import Mathlib.GroupTheory.FiniteAbelian.Duality
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.EulerProduct.ExpLog
import Mathlib.NumberTheory.LSeries.Convergence
import Mathlib.NumberTheory.LSeries.Convolution
import Mathlib.NumberTheory.LSeries.Deriv
import Mathlib.NumberTheory.LSeries.SumCoeff
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Inversion and powers of conjugacy classes, and the size of a class

Inversion of a group is compatible with conjugacy: `x` and `y` are conjugate exactly when `x⁻¹` and
`y⁻¹` are (`TauCeti.isConj_inv_iff`). So inversion descends to the conjugacy classes, where it is an
involution, recorded here as an `InvolutiveInv (ConjClasses G)` instance; `C⁻¹` is the class of the
inverses of the members of `C`, and it has the same size as `C`. A class fixed by this involution is
a **real** class (`TauCeti.IsRealClass`).

Powering likewise commutes with conjugation, so for a **monoid** `M` it too descends to the
conjugacy classes: `ConjClasses.pow C j`, written `C ^ j`, is the class of the `j`-th powers of
the members of `C`.

The other fact collected here is that the size of a conjugacy class is the index of the centralizer
of any of its members, and so divides the order of the group: the orbit-stabilizer theorem for the
conjugation action.

## Main statements

* `TauCeti.isConj_inv_iff`: conjugacy is inherited by inverses in both directions.
* `ConjClasses.inv_mk`: the inverse of the class of `g` is the class of `g⁻¹`.
* `TauCeti.IsRealClass`: a class containing an element conjugate to its own inverse, with
  `TauCeti.isRealClass_iff_inv_eq` identifying it with being fixed by inversion.
* `ConjClasses.ncard_carrier_inv` and `ConjClasses.card_carrier_inv`: a conjugacy
  class and its inverse have the same size, in `Set.ncard` and in `Nat.card` form.
* `ConjClasses.ncard_carrier_mk` and `ConjClasses.card_carrier_mk`: the size of a
  conjugacy class is the index of the centralizer of any of its members, in `Set.ncard` and in
  `Nat.card` form.
* `ConjClasses.ncard_carrier_mk_of_mem_center`: the class of a central element is a single
  point.
* `ConjClasses.card_carrier_mul_orderOf_dvd`: the class size times the order of a member
  divides the order of the group, so the quotient below is an exact ratio.
* `ConjClasses.card_div_card_carrier_mul_orderOf_pos`: for a finite group that ratio is positive.
* `ConjClasses.card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf`: that
  quotient equals the order of the centralizer divided by the order of the member.
* `ConjClasses.one_div_orderOf_div_card_div_card_carrier_mul_orderOf`: dividing `1 / orderOf σ`
  by that quotient, in a semifield of characteristic zero, leaves `#C / #G`.
* `ConjClasses.ncard_carrier_mk_eq_card_filter` and
  `ConjClasses.card_carrier_mk_eq_card_filter`: the size of a conjugacy class as the
  cardinality of a `Finset`, which makes it computable.
* `ConjClasses.card_carrier_dvd_card`: the size of a conjugacy class divides the order of
  the group, with `ConjClasses.card_carrier_cast_ne_zero` the consequence that the size of
  a class is nonzero in any semiring where the group order is, and
  `ConjClasses.card_carrier_div_card_ne_zero` the nonvanishing of `#C / #G` for a finite group.
* `ConjClasses.pow`: the power operation itself, with `C ^ j` its notation.
* `ConjClasses.mem_pow_iff`: an element lies in `C ^ j` exactly when it is a
  `j`-th power of a member of `C`, with `ConjClasses.mk_pow` the computation rule.
* `ConjClasses.pow_zero`, `ConjClasses.pow_one` and
  `ConjClasses.pow_mul`: the identity and composition laws for that power.
* `ConjClasses.map_mk`: the computation rule for `ConjClasses.map` on representatives,
  with `ConjClasses.map_pow` the consequence that the power is natural in the monoid.
* `ConjClasses.mk_ne_mk_of_orderOf_ne`: elements of different orders lie in different conjugacy
  classes.

## Implementation notes

The inversion is an instance rather than a plain function so that the notation `C⁻¹`, the
involutivity lemma `inv_inv` and the reindexing equivalence `Equiv.inv` are all available for
conjugacy classes. Powering is instead a named definition `ConjClasses.pow` with a `Pow` instance
delegating to it, so that the roadmap's `C.pow j` and the notation `C ^ j` are the same function;
the lemmas below are all stated in the `^` form. There is still no
multiplication on `ConjClasses M` — `Pow (ConjClasses M) ℕ` is a bare power operation, not the
`npow` field of a monoid structure, and none of the lemmas here presuppose one.

The power operation is developed for the Chebotarev roadmap (`Chebotarev/README.md` Layer 1,
"consumed Frobenius classes and powers of conjugacy classes", whose `Suggested.lean` pins these
signatures); its consumer there is the von Mangoldt fibre, which sums over the classes `C ^ j`.
That is also why a `pow_two_cyclicFour` regression is kept: a group of
exponent two has no proper nonidentity square, so it cannot separate a correct power operation
from one that collapses to the identity. It is `private`, being a check on this development
rather than reusable conjugacy-class API. This operation is *not* adapted from the
Birkbeck–Brasca `chebotarev-density` development, which works with `ConjClasses.mk` and
`Subgroup.zpowers` directly and never forms `C ^ j`.

The two arithmetic statements concern the quotient `#G / (#C * orderOf σ)`. The first says the
division is exact — `#C` is the index of the centralizer of `σ`, and `orderOf σ` divides that
centralizer's order, so their product divides `#G` — and the second evaluates the quotient as the
centralizer's order over `orderOf σ`. Neither asserts that either side counts anything; a caller
wanting a cardinality interpretation must supply it.
-/

 section

namespace TauCeti

variable {G : Type*} [Group G]





end TauCeti

namespace ConjClasses

variable {G : Type*} [Group G]



























end ConjClasses

namespace TauCeti

variable {G : Type*} [Group G]





-- Not a `simp` lemma: `isRealClass_iff_inv_eq` and `ConjClasses.inv_mk` already rewrite the
-- left-hand side to `ConjClasses.mk g⁻¹ = ConjClasses.mk g`, so tagging it makes `simpNF` fail.


end TauCeti

/-! ### The size of a class against the order of a member -/

namespace ConjClasses

-- Source. Both statements are specified by the Chebotarev roadmap. The divisibility is the
-- declaration pinned at `TauCetiRoadmap/Chebotarev/Suggested.lean` lines 377-382, there stated
-- with `[Finite G]`. The quotient identity is `TauCetiRoadmap/Chebotarev/README.md` §8.2, which
-- writes it `#G / (#C * f) = #Centralizer_G(σ) / f` for `f = orderOf σ` and asks for
-- `#C * f ∣ #G` as a separate statement.









end ConjClasses

/-! ### Powers of a conjugacy class -/

namespace ConjClasses

variable {M : Type*} [Monoid M]





/-- The `j`-th power of the class of `a` is the class of `a ^ j`. -/
@[simp]
theorem mk_pow (a : M) (j : ℕ) : ConjClasses.mk a ^ j = ConjClasses.mk (a ^ j) := by
  -- `pow` is sealed, so this is no longer `rfl`: a theorem exported from this module may only
  -- unfold exposed definitions. Go through `pow`'s equation lemma, after which the statement is
  -- exactly `Quotient`'s computation rule for `Quotient.map`.
  change ConjClasses.pow (ConjClasses.mk a) j = ConjClasses.mk (a ^ j)
  rw [ConjClasses.pow]
  exact Quotient.map_mk _ _ _

















end ConjClasses

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Character orthogonality for finite commutative groups

For a finite commutative group `G` and a domain `M` with enough roots of unity, the characters
of `G` are the monoid homomorphisms `G →* Mˣ`. This file records the *column* orthogonality
relation — the one summed over the character group — in both its punctured and its normal form,
and shows that the commutativity it assumes is necessary: the column relation fails for every
finite non-commutative group whenever the number of characters is nonzero in `M`, as it is in
characteristic zero. The underlying group-theoretic fact, that homomorphisms into a
commutative monoid separate elements only in a commutative group, is
`TauCeti.isMulCommutative_of_forall_exists_monoidHom_apply_ne_one` in
`TauCeti.GroupTheory.Commutator`.

## Main results

* `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one`: for `g ≠ 1`, the sum `∑ χ : G →* Mˣ, χ g`
  over all characters vanishes.
* `CommGroup.sum_monoidHom_apply_eq_ite`: the same sum in normal form, `Nat.card G` at `g = 1`
  and `0` elsewhere. This is the shape an indicator-formula consumer wants, and it is the `simp`
  normal form for such a sum.
* `CommGroup.sum_monoidHom_apply_eq_ite`'s tagged form,
  `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite`: summing `(χ σ)⁻¹ * χ g` isolates the single
  element `σ`, giving `Nat.card G` when `g = σ` and `0` otherwise.
* `AddChar.sum_units_mul_eq_neg_one`: a nontrivial additive character of a finite field
  sums to `-1` over the nonzero elements, even after multiplication by a unit.
* `TauCeti.sum_monoidHom_apply_eq_card_of_mem_commutator`: at an element of the commutator
  subgroup the character sum is the number of characters, every summand being `1`.
* `TauCeti.exists_sum_inv_mul_monoidHom_apply_ne_ite`: **column orthogonality fails for every
  finite non-commutative group** whenever the number of characters is nonzero in `M`, as in
  characteristic zero: at the tag `1` and a nontrivial commutator the tagged sum is the number
  of characters, not `0`.

The file also registers `Fintype (G →* Mˣ)`, which Mathlib leaves at `Finite`; without it a
consumer's own character sum does not elaborate, and two ad-hoc `Fintype.ofFinite` introductions
give syntactically distinct sums. That instance needs only `LeftCancelMonoid G`, so it also serves
consumers indexing over the characters of a finite noncommutative group or monoid.

## Row orthogonality and punctured additive-character sums

The companion *row* relation — for a nontrivial `χ : G →* Mˣ`, the sum `∑ g : G, χ g` over the
group vanishes — is already `sum_hom_units_eq_zero` in
`Mathlib/RingTheory/IntegralDomain.lean`, which states exactly that for an arbitrary monoid
homomorphism `G →* R` into a domain. Specialising it to a character is
`sum_hom_units_eq_zero ((Units.coeHom M).comp χ)`, i.e. the Mathlib lemma composed with the
unit coercion and nothing else, so no declaration for it is added. Callers wanting the row
relation should use the Mathlib lemma directly. (`MulChar.sum_eq_zero_of_ne_one` in
`Mathlib/NumberTheory/MulChar/Basic.lean` is the analogous statement in the `MulChar`
vocabulary, for a multiplicative character of a finite commutative monoid valued in a domain.)

The theorem `AddChar.sum_units_mul_eq_neg_one` below is not a restatement of that full row
relation: it removes the zero term from a finite-field additive-character sum and reindexes the
remaining nonzero elements by `Fˣ`. This punctured form is what character computations over a
finite field consume directly.

The column relation genuinely is not in Mathlib in this generality. It appears there only in
specialisations: the `ZMod n` one, `DirichletCharacter.sum_characters_eq_zero` in
`Mathlib/NumberTheory/DirichletCharacter/Orthogonality.lean`, and the finite-additive-group one
over `ℂ`, `AddChar.sum_apply_eq_ite` in
`Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean` (with
`AddChar.sum_apply_eq_zero_iff_ne_zero` beside it). Neither implies the statement below, which is
multiplicative and valued in an arbitrary domain with enough roots of unity rather than in `ℂ`
or over `ZMod n`.

## References

Two of the results are adapted from
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca).

* `CommGroup.sum_monoidHom_apply_eq_zero_of_ne_one` comes from `sum_char_apply_eq_zero_of_ne_one`
  in `CebotarevDensity/ForMathlib/CharacterOrthogonality.lean`, at commit
  `8575c9df1ae0a61120ab5c964c7911414254bec7`.
* `CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` comes from the private
  `sum_galoisCharacter_mul_inv_eq` in `CebotarevDensity/Cyclotomic.lean`, at commit
  `55a89985d47a3befcf6069aca1da250ff088b5c7`, where the argument is attributed to Sharifi,
  *Algebraic Number Theory*, 7.2.1 step (iii), p. 142. The source writes the sum as
  `∑ χ, χ σ * (χ τ)⁻¹` with the inverse on the second argument and concludes `σ * τ⁻¹ = 1`; the
  statement here carries the inverse on the tag and concludes `g = σ`, which is the same identity
  read in the other orientation.
-/

 section

open scoped commutatorElement

namespace AddChar

variable {F : Type*} [Field F] [Fintype F]
variable {R : Type*} [CommRing R] [IsDomain R]



end AddChar

variable {G : Type*} [Finite G] {M : Type*} [CommRing M] [IsDomain M]



namespace CommGroup

variable [CommGroup G] [HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- **Character-column orthogonality** for a finite commutative group `G` valued in a domain `M`
with enough roots of unity: for `g ≠ 1`, the sum of `χ g` over all characters `χ : G →* Mˣ`
vanishes. -/
theorem sum_monoidHom_apply_eq_zero_of_ne_one {g : G} (hg : g ≠ 1) :
    ∑ χ : G →* Mˣ, (χ g : M) = 0 := by
  -- A specialisation of `sum_hom_units_eq_zero` on the dual group `G →* Mˣ` along the
  -- evaluation homomorphism `χ ↦ χ g`.
  obtain ⟨χ₀, hχ₀⟩ := exists_apply_ne_one_of_hasEnoughRootsOfUnity G M hg
  exact sum_hom_units_eq_zero ((Units.coeHom M).comp (MonoidHom.eval g))
    fun h ↦ hχ₀ <| Units.val_eq_one.mp <| DFunLike.congr_fun h χ₀

/-- **Column orthogonality in normal form**: the character sum is `Nat.card G` at the identity
and vanishes elsewhere. This covers both cases at once, and states the identity value as the
cardinality of `G` itself rather than of its dual, which is the shape an indicator-formula
consumer wants. -/
@[simp]
theorem sum_monoidHom_apply_eq_ite [DecidableEq G] (g : G) :
    ∑ χ : G →* Mˣ, (χ g : M) = if g = 1 then (Nat.card G : M) else 0 := by
  split
  · next hg =>
    subst hg
    -- the dual of `G` has the cardinality of `G`, by Mathlib's character duality
    have hcard : Fintype.card (G →* Mˣ) = Nat.card G := by
      simpa using card_monoidHom_of_hasEnoughRootsOfUnity G M
    simp [hcard]
  · next hg => exact sum_monoidHom_apply_eq_zero_of_ne_one hg

/-- **Tagged column orthogonality.** Summing `(χ σ)⁻¹ * χ g` over all characters isolates the
single element `σ`: the sum is `Nat.card G` when `g = σ` and `0` otherwise. This is the form a
fibre-selecting argument uses, `sum_monoidHom_apply_eq_ite` being the case `σ = 1`.

The inverse sits on the tag `σ`, not on the argument `g`. Without it the sum is
`∑ χ, χ (σ * g)`, which is the indicator of `g = σ⁻¹` — a different fibre, and one that genuinely
differs whenever `σ` is not an involution. -/
@[simp]
theorem sum_inv_mul_monoidHom_apply_eq_ite [DecidableEq G] (σ g : G) :
    ∑ χ : G →* Mˣ, (((χ σ)⁻¹ : Mˣ) : M) * ((χ g : Mˣ) : M) =
      if g = σ then (Nat.card G : M) else 0 := by
  have key : ∀ χ : G →* Mˣ, (((χ σ)⁻¹ : Mˣ) : M) * ((χ g : Mˣ) : M) = ((χ (σ⁻¹ * g) : Mˣ) : M) :=
    fun χ ↦ by rw [map_mul, map_inv, Units.val_mul]
  simp only [key, sum_monoidHom_apply_eq_ite, inv_mul_eq_one, eq_comm]

end CommGroup

namespace TauCeti

variable [Group G]





end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The ideal von Mangoldt function

The von Mangoldt function of a nonzero ideal `A` of the ring of integers of a number field is
`log N(P)` when `A` is a positive power of a prime ideal `P`, and zero otherwise.  This file
packages that function as an `IdealArithmeticFunction` and defines its pointwise product with an
ideal arithmetic function.

## Main definitions

* `TauCeti.IdealArithmeticFunction.vonMangoldt` is the complex-valued ideal von Mangoldt
  function.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform` sends `f` to the weighted function
  `A ↦ f(A) Λ(A)`.

## Main results

* `TauCeti.IdealArithmeticFunction.vonMangoldt_apply_prime_pow` computes the value on a positive
  power of a prime ideal.
* `TauCeti.IdealArithmeticFunction.vonMangoldt_ne_zero_iff` says that its support is exactly the
  prime-power ideals.
* `TauCeti.IdealArithmeticFunction.vonMangoldtTransform_ne_zero_iff` identifies the support of
  the transform, and its specialization in `TauCeti.MultiplicativeIdealWeight` describes this as
  the good prime powers for a completely multiplicative weight.

The definition chooses a prime base from a proof that `A` is a prime power.  Mathlib's
`eq_of_prime_pow_eq`, applied to ideals, identifies that choice with any prime base supplied by a
caller.  The public evaluation theorem therefore removes the choice from every computation.

## Implementation notes

This is the ideal analogue of Mathlib's `ArithmeticFunction.vonMangoldt`.  Here the prime base is
chosen from `IsPrimePow` rather than computed by `Nat.minFac`, its logarithmic weight is
`Ideal.absNorm P` rather than `p`, and the function is complex-valued to match
`IdealArithmeticFunction`.

## Roadmap role

This is the algebraic part of Layer **2.3** of
`TauCetiRoadmap/ArithmeticDirichletSeries/README.md`.  The logarithmic-derivative identity named in
that target additionally requires the Euler-product package of Layer 3; this file supplies its
coefficient and exact prime-power support in advance.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
-/

 section

namespace TauCeti

open _root_.NumberField
open scoped _root_.nonZeroDivisors _root_.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- The absolute norm of a prime ideal is greater than one. -/
theorem one_lt_absNorm_of_prime {P : Ideal (𝓞 K)} (hP : Prime P) :
    1 < Ideal.absNorm P := by
  rw [Nat.one_lt_iff_ne_zero_and_ne_one]
  exact ⟨Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero,
    Ideal.absNorm_eq_one_iff.not.mpr fun htop ↦
      hP.not_isUnit (Ideal.isUnit_iff.mpr htop)⟩

namespace IdealArithmeticFunction





/-- The value of the ideal von Mangoldt function at a positive power of a prime ideal.  This is the
choice-free characterization of `vonMangoldt` on its support. -/
theorem vonMangoldt_apply_of_eq_prime_pow {A : (Ideal (𝓞 K))⁰} {P : Ideal (𝓞 K)}
    (hP : Prime P) {n : ℕ} (hn : 0 < n) (hpow : P ^ n = (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = Real.log (Ideal.absNorm P) := by
  have hA : IsPrimePow (A : Ideal (𝓞 K)) := ⟨P, n, hP, hn, hpow⟩
  have hchosen : hA.choose = P := by
    exact eq_of_prime_pow_eq hA.choose_spec.choose_spec.1 hP
      hA.choose_spec.choose_spec.2.1 (hA.choose_spec.choose_spec.2.2.trans hpow.symm)
  rw [vonMangoldt, dif_pos hA, hchosen]





/-- The ideal von Mangoldt function vanishes away from prime powers. -/
@[simp]
theorem vonMangoldt_eq_zero_of_not_isPrimePow {A : (Ideal (𝓞 K))⁰}
    (hA : ¬ IsPrimePow (A : Ideal (𝓞 K))) :
    (vonMangoldt : IdealArithmeticFunction K) A = 0 := by
  simp [vonMangoldt, hA]





private theorem exists_ofReal_eq_vonMangoldt (A : (Ideal (𝓞 K))⁰) :
    ∃ r : ℝ, 0 ≤ r ∧ (vonMangoldt : IdealArithmeticFunction K) A = (r : ℂ) := by
  by_cases hA : IsPrimePow (A : Ideal (𝓞 K))
  · obtain ⟨P, n, hP, hn, hpow⟩ := hA
    refine ⟨Real.log (Ideal.absNorm P), Real.log_nonneg ?_,
      vonMangoldt_apply_of_eq_prime_pow hP hn hpow⟩
    exact_mod_cast (one_lt_absNorm_of_prime hP).le
  · exact ⟨0, le_rfl, vonMangoldt_eq_zero_of_not_isPrimePow hA⟩

/-- Every value of the ideal von Mangoldt function is real. -/
theorem vonMangoldt_im {A : (Ideal (𝓞 K))⁰} :
    ((vonMangoldt : IdealArithmeticFunction K) A).im = 0 := by
  obtain ⟨r, -, hr⟩ := exists_ofReal_eq_vonMangoldt A
  rw [hr, Complex.ofReal_im]







/-- Evaluation of the von Mangoldt transform. -/
theorem vonMangoldtTransform_apply (f : IdealArithmeticFunction K)
    (A : (Ideal (𝓞 K))⁰) :
    f.vonMangoldtTransform A = f A * vonMangoldt A := by
  rw [vonMangoldtTransform, Pi.mul_apply]







end IdealArithmeticFunction

namespace MultiplicativeIdealWeight





end MultiplicativeIdealWeight

end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Chebyshev's `ψ` for a set of prime ideals, and the removal of the higher prime powers

For a set `S` of height-one primes of the ring of integers of a number field `K`, Chebyshev's
`ψ` weights *every* prime power `𝔭 ^ k` with `𝔭 ∈ S` and `k ≥ 1` by `log N(𝔭)`, while `ϑ` weights
only the primes themselves.  This file defines `ψ`, proves that the difference `ψ - ϑ` is exactly
the higher-prime-power sum estimated in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/HigherPrimePowers.lean`, and spends that estimate
on the transfer of an asymptotic `ψ(x) = δ x + o(x)` to `ϑ(x) = δ x + o(x)`.

Prime powers with `k ≥ 2` are kept visible throughout: `ψ` is *defined* with all of them present,
and their removal is a named hypothesis, `TauCeti.HasNegligibleHigherPrimePowers`, discharged for
the standard logarithmic weight by `TauCeti.standardPrimePowerRemoval`.  A different coefficient
system does not get that hypothesis for free; what it has to supply is the domination bound of
`TauCeti.primePowerSummatory_isLittleO_of_le_higherPrimePowerWeight`.

## Main definitions

* `TauCeti.primePowerWeight` is the standard logarithmic prime-power weight, the value `log N(𝔭)`
  at `𝔭 ^ k` for every `k ≥ 1`.  It is the real form of the ideal von Mangoldt function of Layer 2
  on the prime powers.
* `TauCeti.primePsi` is its inclusive summatory function over the prime powers whose base lies in
  `S`: the number-field analogue of Chebyshev's `ψ`.
* `TauCeti.HasNegligibleHigherPrimePowers K S` says that `ψ - ϑ` is `o(x)`.
* `TauCeti.primeVonMangoldtWeight` is the same weight spread over *all* nonzero ideals, zero away
  from the prime powers with base in `S`, and `TauCeti.primeVonMangoldtCoeff` is its regrouping by
  absolute norm, an `ArithmeticFunction ℝ`.

## Main results

* `TauCeti.primePowerSummatory_indicator_sub_primeTheta` splits the exponent-one part off the
  standard weight restricted to any set of prime powers containing exactly the primes of `S`.
* `TauCeti.primePsi_sub_primeTheta` identifies `ψ - ϑ` with the higher-prime-power sum.
* `TauCeti.primePsi_le_ncard_mul_log`: for `x ≥ 1`, a finite set of primes contributes at most
  `#S · log x` to `ψ`, with `TauCeti.primePsi_isBigO_log_of_finite` and
  `TauCeti.primePsi_isLittleO_of_finite` its asymptotic forms.
* `TauCeti.standardPrimePowerRemoval` proves `HasNegligibleHigherPrimePowers K S` for every `S`,
  from the Layer 5 estimate `ψ(x) - ϑ(x) = O(√x log² x)`.
* `TauCeti.primeTheta_asymptotic_of_primePsi` and
  `TauCeti.primePsi_asymptotic_of_primeTheta` transfer a linear asymptotic across that difference,
  with `TauCeti.primeTheta_isEquivalent_of_primePsi` the equivalence form for a nonzero density.
* `TauCeti.primePsi_eq_sum_range` presents `ψ(x)` as the inclusive partial sum
  `∑_{n ≤ ⌊x⌋₊} a n` of the coefficient system, whose coefficients are nonnegative
  (`TauCeti.primeVonMangoldtCoeff_nonneg`) and supported on the prime powers
  (`TauCeti.primeVonMangoldtCoeff_eq_zero_of_not_isPrimePow`).
* `TauCeti.normCoeff_vonMangoldt` identifies the coefficient system of the full prime carrier with
  the Layer 1 regrouping of the Layer 2 ideal von Mangoldt function.
* `TauCeti.primeVonMangoldtCoeff_rat_natGenerator_pow` evaluates the coefficient system of any set
  of primes of `𝓞 ℚ` at a prime power, and `TauCeti.primeVonMangoldtCoeff_rat_le` bounds it by
  Mathlib's von Mangoldt function `Λ`.

## Roadmap role

This is Layer **10.2** of `TauCetiRoadmap/ArithmeticDirichletSeries/README.md`: "For the fixed
standard nonnegative logarithmic prime-power weight, use Layer 5 to prove
`standardPrimePowerRemoval : HasNegligibleHigherPrimePowers K S` and make
`primeTheta_asymptotic_of_primePsi` consume that named estimate."  It also supplies the arithmetic
half of Layer **10.1**, "Define `primePsi` with all prime powers present": the exact nonnegative
von Mangoldt coefficient system and the identity presenting `ψ` as its partial sum, which is the
shape in which a Tauberian theorem delivers its conclusion.  The analytic boundary package and
the resulting prime-number-theorem transfer are in
`TauCeti/NumberTheory/ArithmeticDirichletSeries/Prime/Boundary.lean`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 7.
* G. Tenenbaum, *Introduction to Analytic and Probabilistic Number Theory*, Chapter I.2.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII.

The rational-prime case of `ψ`, `ϑ` and their difference is Mathlib's
`Mathlib/NumberTheory/Chebyshev.lean`, whose `Chebyshev.theta_le_psi` and
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log` are the analogues of
`TauCeti.primeTheta_le_primePsi` and `TauCeti.standardPrimePowerRemoval`; nothing is transported
from there, since the estimate consumed here is proved over prime ideals in Layer 5.
-/

 section

namespace TauCeti

open _root_.Filter _root_.NumberField
open scoped _root_.Asymptotics _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain

variable {K : Type*} [Field K] [NumberField K]

/-! ### The standard logarithmic prime-power weight -/



/-- The standard logarithmic prime-power weight is the real part of the ideal von Mangoldt
function of Layer 2, restricted to the prime powers. -/
theorem primePowerWeight_eq_vonMangoldt_re (A : IdealPrimePower K) :
    primePowerWeight A = (IdealArithmeticFunction.vonMangoldt (A : (Ideal (𝓞 K))⁰)).re := by
  rw [primePowerWeight, IdealArithmeticFunction.vonMangoldt_apply_of_eq_prime_pow
    (prime_primePowerBase A) (primePowerExponent_pos A)
    (primePowerBase_pow_primePowerExponent A), Complex.ofReal_re]

/-- On a prime-power ideal the ideal von Mangoldt function is the standard logarithmic weight,
as a complex number. -/
@[simp]
theorem vonMangoldt_eq_primePowerWeight (A : IdealPrimePower K) :
    (IdealArithmeticFunction.vonMangoldt : IdealArithmeticFunction K) A =
      (primePowerWeight A : ℂ) :=
  Complex.ext (by rw [primePowerWeight_eq_vonMangoldt_re, Complex.ofReal_re])
    (by rw [IdealArithmeticFunction.vonMangoldt_im, Complex.ofReal_im])









/-! ### Chebyshev's `ψ` -/



variable {S : Set (HeightOneSpectrum (𝓞 K))} {x δ : ℝ}











/-! ### The higher prime powers as the gap between `ψ` and `ϑ` -/







/-! ### Removing the higher prime powers -/



















/-! ### The von Mangoldt coefficient system of a set of primes -/

















































end TauCeti

end
end

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Character orthogonality for the ideal weight of a Galois character

For a finite **abelian** Galois extension `L / K` of number fields, summing `(χ σ)⁻¹` against the
ideal weight `MonoidHom.galoisCharacterWeight χ` over all characters `χ : Gal(L/K) →* ℂˣ` selects
one Frobenius fibre: at a height-one prime `𝔭` unramified in `L` the sum is `#Gal(L/K)` when the
Frobenius at `𝔭` is `σ`, and `0` otherwise. At a ramified prime it is `0`, because every summand is.

What the identity buys is a change of index: an indicator of the single condition `Frob 𝔭 = σ`
becomes a sum over the character group, in which each character contributes an ideal weight that is
completely multiplicative, and so is open to Euler-product and Dirichlet-series methods.

## Main results

* `AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_of_unramified`: the orthogonality identity at
  an unramified height-one prime, selecting the fibre of a chosen `σ`.
* `AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified`: the same identity for the
  `j`-th power of the weight, selecting the primes whose Frobenius has `j`-th power `σ`.
* `AlgEquiv.sum_inv_mul_galoisCharacterWeight_apply_eq_zero_of_mem_ramifiedPrimes`: the sum
  vanishes at a ramified prime, for the trivial reason that every summand does.

## Implementation notes

The inverse sits on the tag `σ`, never on the Frobenius argument. Without it the sum is
`∑ χ, χ (σ * Frob 𝔭)`, the indicator of `Frob 𝔭 = σ⁻¹`, which is a different fibre whenever `σ` is
not an involution.

Commutativity enters as `[IsMulCommutative (L ≃ₐ[K] L)]`, a `Prop`-class, rather than as a
`CommGroup` instance argument: `L ≃ₐ[K] L` already carries a `Group` instance, and a second
bundled group structure on the same type would be a diamond. Mathlib supplies the bundled form
from the mixin as a `scoped instance` in the `IsMulCommutative` namespace, deliberately kept out of
global synthesis, so the proofs open that scope. The abelian hypothesis is what
`CommGroup.sum_inv_mul_monoidHom_apply_eq_ite` requires; `Gal(K(ζ_m)/K)` satisfies it by
`IsCyclotomicExtension.Aut.commGroup`.

The sum ranges over the full character group, whose cardinality equals `Nat.card (L ≃ₐ[K] L)` by
Mathlib's duality for finite abelian groups; that equality is what puts `Nat.card (L ≃ₐ[K] L)` on
the right rather than the cardinality of the dual.

## References

The orthogonality relation and its use to select a Frobenius fibre are adapted from
`sum_galoisCharacter_mul_inv_eq` and the pair `character_orthogonality_cyclotomic_eq` /
`character_orthogonality_cyclotomic_ne` in `CebotarevDensity/Cyclotomic.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `55a89985d47a3befcf6069aca1da250ff088b5c7`, which attributes the
argument to Sharifi, *Algebraic Number Theory*, 7.2.1 step (iii), p. 142. The statements here are
in `if`-normal form rather than split into matching and non-matching cases, are taken at the level
of the ideal weight rather than of `χ (Frob 𝔭)` directly, and hold for a general abelian extension
rather than a cyclotomic one.
-/

 section

open scoped _root_.NumberField

open _root_.IsDedekindDomain (HeightOneSpectrum)

open _root_.NumberField _root_.NumberField.Chebotarev

namespace AlgEquiv

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]



open scoped Classical IsMulCommutative in
/-- **Character orthogonality for a power of the Galois character weight.** For `L / K` abelian,
`σ` a chosen element of `Gal(L/K)`, `𝔭` a height-one prime unramified in `L` and `j` a natural
number, summing `(χ σ)⁻¹` against the `j`-th power of the weight at `𝔭` gives `#Gal(L/K)` when
the `j`-th power of the Frobenius at `𝔭` is `σ`, and `0` otherwise.

This is the form the prime-power terms of a logarithmic derivative need: the weight at `𝔭 ^ j` is
`χ (Frob 𝔭) ^ j = χ (Frob 𝔭 ^ j)`, so the power lands on the Frobenius argument and the inverse
stays on the tag. -/
theorem sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified
    [IsMulCommutative (L ≃ₐ[K] L)] (σ : L ≃ₐ[K] L) (𝔭 : HeightOneSpectrum (𝓞 K))
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (j : ℕ) :
    haveI : 𝔭.asIdeal.IsMaximal := 𝔭.isMaximal
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := L) χ 𝔭.asIdeal ^ j =
      if (artinSymbol (L := L) 𝔭.asIdeal hur).out ^ j = σ then (Nat.card (L ≃ₐ[K] L) : ℂ)
      else 0 := by
  have hexp : Monoid.exponent (L ≃ₐ[K] L) ≠ 0 := Monoid.exponent_ne_zero_of_finite
  have : NeZero ((Monoid.exponent (L ≃ₐ[K] L) : ℕ) : ℂ) := ⟨Nat.cast_ne_zero.mpr hexp⟩
  calc ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * MonoidHom.galoisCharacterWeight (L := L) χ 𝔭.asIdeal ^ j
      = ∑ χ : (L ≃ₐ[K] L) →* ℂˣ,
          (((χ σ)⁻¹ : ℂˣ) : ℂ) * ((χ ((artinSymbol (L := L) 𝔭.asIdeal hur).out ^ j) : ℂˣ) : ℂ) :=
        Finset.sum_congr rfl fun χ _ ↦ by
          rw [MonoidHom.galoisCharacterWeight_apply_of_unramified χ 𝔭 hur, map_pow,
            Units.val_pow_eq_pow_val]
    _ = _ := CommGroup.sum_inv_mul_monoidHom_apply_eq_ite _ _



end AlgEquiv

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Frobenius von Mangoldt coefficients

For a conjugacy class `C` in the Galois group of a finite Galois extension `L / K`, this file
defines the von Mangoldt coefficient and summatory functions restricted to `C`. A prime power
`𝔭 ^ j` belongs to the `C`-fibre when the `j`-th power of the Artin class of `𝔭` is `C`.
Consequently a prime whose Artin class is not `C` can still contribute through a higher power.

The definitions retain only unramified primes: the Artin symbol is never evaluated at a ramified
prime. The exponent-one terms form `frobeniusTheta`; all higher prime powers are dominated by the
unrestricted higher-prime-power weight from the arithmetic Dirichlet-series development, hence
their contribution is `o(x)`.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimePowerSet`: prime powers selected by the powered Artin
  class.
* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff`: the corresponding nonnegative arithmetic
  function, regrouped by absolute norm.
* `NumberField.Chebotarev.frobeniusPsi` and `NumberField.Chebotarev.frobeniusTheta`: the weighted
  prime-power and prime summatory functions.
* `NumberField.Chebotarev.frobeniusPrimeCount`: the number of primes of norm at most `x`
  whose arithmetic Frobenius class is `C`, with `NumberField.Chebotarev.natCast_frobeniusPrimeCount`
  identifying it with the generic count of `frobeniusPrimeSet`.

## Main results

* `NumberField.Chebotarev.frobeniusVonMangoldtCoeff_rat_natGenerator_pow`: over `ℚ`, the
  coefficient at `p ^ (k + 1)` is the powered Frobenius weight of `𝔭 ^ (k + 1)`, the only ideal
  of that norm.
* `NumberField.Chebotarev.frobeniusPsi_eq_sum_range`: `frobeniusPsi` is the inclusive partial sum
  of `frobeniusVonMangoldtCoeff`.
* `NumberField.Chebotarev.frobeniusPsi_eq_sum_Icc`: the same sum indexed from `1`.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_eq_primePowerSummatory`: their
  difference is exactly the contribution from exponents at least two.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_le`: that difference is bounded by
  the unrestricted higher-prime-power tail.
* `NumberField.Chebotarev.frobeniusPsi_sub_frobeniusTheta_isLittleO`: this difference is `o(x)`.

The coefficient convention follows Neukirch, *Algebraic Number Theory*, Chapter VII. The
construction reuses Tau Ceti's generic prime-power counting and removal estimates.
-/

 section

namespace NumberField.Chebotarev

open _root_.Filter _root_.TauCeti
open scoped _root_.Asymptotics _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

-- The powered-class convention follows `TauCetiRoadmap/Chebotarev/Suggested.lean`.


/-- Membership in `frobeniusPrimePowerSet`, unfolded. -/
@[simp]
theorem mem_frobeniusPrimePowerSet_iff {A : IdealPrimePower K}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    A ∈ frobeniusPrimePowerSet K L C ↔
      ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
          Algebra.IsUnramifiedAt (𝓞 K) Q,
        artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C :=
  Iff.rfl

/-- With an unramifiedness proof fixed, membership in the powered Frobenius fibre is the stated
equality of conjugacy classes. In particular, membership is independent of that proof. -/
theorem mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq {A : IdealPrimePower K}
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q) (C : ConjClasses (L ≃ₐ[K] L)) :
    A ∈ frobeniusPrimePowerSet K L C ↔
      artinSymbol (primePowerBase A).asIdeal hur ^ primePowerExponent A = C :=
  ⟨fun ⟨_, h⟩ ↦ h, fun h ↦ ⟨hur, h⟩⟩

-- Not `@[simp]`: `mem_frobeniusPrimePowerSet_iff` together with `primePowerBase_ofPrime`,
-- `primePowerExponent_ofPrime` and `ConjClasses.pow_one` already rewrites the left-hand side.




/-- A prime power in the `C`-fibre has weight `log N(𝔭)`. -/
@[simp]
theorem frobeniusPrimePowerWeight_of_mem {C : ConjClasses (L ≃ₐ[K] L)}
    {A : IdealPrimePower K} (hA : A ∈ frobeniusPrimePowerSet K L C) :
    frobeniusPrimePowerWeight K L C A = primePowerWeight A := by
  rw [frobeniusPrimePowerWeight, Set.indicator_of_mem hA]



/-- A prime power outside the `C`-fibre has weight zero. -/
@[simp]
theorem frobeniusPrimePowerWeight_of_notMem {C : ConjClasses (L ≃ₐ[K] L)}
    {A : IdealPrimePower K} (hA : A ∉ frobeniusPrimePowerSet K L C) :
    frobeniusPrimePowerWeight K L C A = 0 :=
  Set.indicator_of_notMem hA _

































/-- On the prime-power carrier, the ideal weight is the powered Frobenius weight. -/
@[simp]
theorem frobeniusVonMangoldtWeight_idealPrimePower (C : ConjClasses (L ≃ₐ[K] L))
    (A : IdealPrimePower K) :
    frobeniusVonMangoldtWeight K L C (A : (Ideal (𝓞 K))⁰) =
      frobeniusPrimePowerWeight K L C A := by
  simp [frobeniusVonMangoldtWeight, A.2]

/-- The ideal weight vanishes away from prime-power ideals. -/
@[simp]
theorem frobeniusVonMangoldtWeight_eq_zero_of_not_isPrimePow
    (C : ConjClasses (L ≃ₐ[K] L)) {I : (Ideal (𝓞 K))⁰}
    (hI : ¬ IsPrimePow (I : Ideal (𝓞 K))) : frobeniusVonMangoldtWeight K L C I = 0 := by
  simp [frobeniusVonMangoldtWeight, hI]









-- The powered filter is exercised here: this is the term a definition filtering on
-- `artinSymbol 𝔭 = C` alone would lose. The order-four configuration is not vacuous —
-- `ConjClasses.mk_ne_mk_of_orderOf_ne` separates the two classes for *every* element of order
-- four, its square having order two, and the cyclic group of order four realises such an element
-- concretely.




















end NumberField.Chebotarev

end
end

section
set_option autoImplicit true
namespace TauCeti
end TauCeti
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The Frobenius von Mangoldt series as a character sum of logarithmic derivatives

Let `L / K` be a finite **abelian** Galois extension of number fields with group `G`, and fix
`σ ∈ G`. For each character `χ : G →* ℂˣ` let `L_χ` be the `L`-series of the Galois character
weight `MonoidHom.galoisCharacterWeight χ`, whose Euler product omits the primes ramified in `L`.
This file proves, for `Re s > 1`,

```text
∑_{𝔭 unramified, m ≥ 1, Frob(𝔭)^m = σ} log N𝔭 · N𝔭^{-ms}
  = (1 / #G) ∑_χ χ(σ)⁻¹ · (-L_χ'(s) / L_χ(s)).
```

The left-hand side is the `LSeries` of the canonical coefficient
`NumberField.Chebotarev.frobeniusVonMangoldtCoeff`, so the identity is a theorem about that
coefficient rather than a hypothesis on an arbitrary sequence. It reduces the
Frobenius-restricted von Mangoldt series to the logarithmic derivatives of the one-dimensional
character series, which is the form the Tauberian step of the Chebotarev argument consumes.

The proof is termwise. By
`TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform` each
`-L_χ'/L_χ` is the ideal-indexed series of `χ(A) Λ(A)`. At a prime power `A = 𝔭 ^ m` the
weight is `χ(Frob 𝔭) ^ m = χ(Frob(𝔭) ^ m)` when `𝔭` is unramified and `0` otherwise, and
character orthogonality
(`AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified`) collapses the character
sum at `A` to `#G` times the indicator of `Frob(𝔭) ^ m = σ`. That indicator is exactly the powered
filter of `frobeniusVonMangoldtWeight`, since in an abelian group the class of `Frob(𝔭) ^ m` is
`{σ}` precisely when `Frob(𝔭) ^ m = σ`.

## Main results

* `NumberField.Chebotarev.sum_inv_mul_vonMangoldtTransform_galoisCharacterWeight_apply`: the
  character sum of the von Mangoldt transforms at one nonzero ideal is `#G` times the Frobenius
  von Mangoldt weight of `σ` there.
* `NumberField.Chebotarev.LSeriesSummable_frobeniusVonMangoldtCoeff`: the Frobenius von Mangoldt
  series converges absolutely on `Re s > 1`, for an arbitrary conjugacy class.
* `NumberField.Chebotarev.LSeries_frobeniusVonMangoldtCoeff_eq_sum_logDeriv`: the character
  expansion of the Frobenius von Mangoldt series.

## Implementation notes

The inverse sits on the tag `σ`, never on the Frobenius argument. Writing `χ σ` for `(χ σ)⁻¹`, or
`χ (Frob 𝔭)⁻¹` for `χ (Frob 𝔭)`, replaces the fibre of `σ` by the fibre of `σ⁻¹`.

The prime-power filter uses the power of the Frobenius, not the Frobenius itself: the term at
`𝔭 ^ m` is counted when `Frob(𝔭) ^ m = σ`, even if `Frob 𝔭 ≠ σ`. This is what
`frobeniusVonMangoldtWeight` records and what the orthogonality at the `m`-th power of the weight
produces, so no separate bookkeeping of the higher prime powers is needed here.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

 section

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

open _root_.TauCeti
open scoped _root_.nonZeroDivisors _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical IsMulCommutative in
/-- **Character orthogonality for the von Mangoldt transforms.** For `L / K` abelian and `σ` in its
Galois group, summing `(χ σ)⁻¹` against the von Mangoldt transform of the Galois character weight
at a nonzero ideal `I` gives `#Gal(L/K)` times the Frobenius von Mangoldt weight of `σ` at `I`.

At `I = 𝔭 ^ m` with `𝔭` unramified this is `#Gal(L/K) · log N𝔭` when `Frob(𝔭) ^ m = σ` and `0`
otherwise; at a ramified prime power, and away from the prime powers, both sides vanish. -/
theorem solution
    [_root_.IsMulCommutative (L ≃ₐ[K] L)] (σ : L ≃ₐ[K] L) (I : (_root_.Ideal (𝓞 K))⁰) :
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ, (((χ σ)⁻¹ : ℂˣ) : ℂ) *
        (_root_.MonoidHom.galoisCharacterWeight (L := L) χ).toIdealArithmeticFunction.vonMangoldtTransform
          I =
      (_root_.Nat.card (L ≃ₐ[K] L) : ℂ) * (_root_.NumberField.Chebotarev.frobeniusVonMangoldtWeight K L (_root_.ConjClasses.mk σ) I : ℂ) := by
  by_cases hI : _root_.IsPrimePow (I : _root_.Ideal (𝓞 K))
  swap
  · simp only [_root_.TauCeti.IdealArithmeticFunction.vonMangoldtTransform_apply,
      _root_.TauCeti.IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hI, _root_.MulZeroClass.mul_zero,
      _root_.Finset.sum_const_zero, _root_.NumberField.Chebotarev.frobeniusVonMangoldtWeight_eq_zero_of_not_isPrimePow _ hI,
      _root_.Complex.ofReal_zero]
  set A : _root_.TauCeti.IdealPrimePower K := ⟨I, hI⟩
  have hA : (A : (_root_.Ideal (𝓞 K))⁰) = I := _root_.rfl
  have hpow := _root_.TauCeti.primePowerBase_pow_primePowerExponent A
  have hm := _root_.TauCeti.primePowerExponent_pos A
  have hterm : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ,
      (_root_.MonoidHom.galoisCharacterWeight (L := L) χ).toIdealArithmeticFunction.vonMangoldtTransform
          I =
        _root_.MonoidHom.galoisCharacterWeight (L := L) χ (_root_.TauCeti.primePowerBase A).asIdeal ^
            _root_.TauCeti.primePowerExponent A * (_root_.TauCeti.primePowerWeight A : ℂ) := fun χ ↦ by
    rw [_root_.TauCeti.IdealArithmeticFunction.vonMangoldtTransform_apply, ← hA, _root_.TauCeti.vonMangoldt_eq_primePowerWeight,
      _root_.TauCeti.MultiplicativeIdealWeight.toIdealArithmeticFunction_apply, ← hpow, _root_.map_pow]
  simp only [hterm, ← _root_.mul_assoc, ← _root_.Finset.sum_mul]
  rw [← hA, _root_.NumberField.Chebotarev.frobeniusVonMangoldtWeight_idealPrimePower]
  by_cases hur : ∀ (Q : _root_.Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (_root_.TauCeti.primePowerBase A).asIdeal],
      _root_.Algebra.IsUnramifiedAt (𝓞 K) Q
  · have : (_root_.TauCeti.primePowerBase A).asIdeal.IsMaximal := (_root_.TauCeti.primePowerBase A).isMaximal
    rw [_root_.AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified σ _ hur]
    have hmem : A ∈ _root_.NumberField.Chebotarev.frobeniusPrimePowerSet K L (_root_.ConjClasses.mk σ) ↔
        (_root_.NumberField.artinSymbol (L := L) (_root_.TauCeti.primePowerBase A).asIdeal hur).out ^ _root_.TauCeti.primePowerExponent A = σ := by
      have hout : _root_.ConjClasses.mk (_root_.NumberField.artinSymbol (L := L) (_root_.TauCeti.primePowerBase A).asIdeal hur).out =
          _root_.NumberField.artinSymbol (L := L) (_root_.TauCeti.primePowerBase A).asIdeal hur := _root_.Quotient.out_eq' _
      rw [_root_.NumberField.Chebotarev.mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hur, ← hout, _root_.ConjClasses.mk_pow,
        _root_.ConjClasses.mk_eq_mk_iff_isConj, _root_.isConj_iff_eq, hout]
    split_ifs with h
    · rw [_root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_mem (hmem.mpr h)]
    · rw [_root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_notMem (_root_.mt hmem.mp h), _root_.MulZeroClass.zero_mul, _root_.Complex.ofReal_zero,
        _root_.MulZeroClass.mul_zero]
  · have hram : _root_.TauCeti.primePowerBase A ∈ _root_.NumberField.Chebotarev.ramifiedPrimes K L :=
      (_root_.NumberField.Chebotarev.mem_ramifiedPrimes_iff (L := L) _).mpr hur
    have hnot : A ∉ _root_.NumberField.Chebotarev.frobeniusPrimePowerSet K L (_root_.ConjClasses.mk σ) := fun h ↦
      hur (mem_frobeniusPrimePowerSet_iff.mp h).1
    simp only [(_root_.MonoidHom.galoisCharacterWeight_apply_eq_zero_iff _ _).mpr hram,
      _root_.zero_pow hm.ne', _root_.MulZeroClass.mul_zero, _root_.Finset.sum_const_zero, _root_.MulZeroClass.zero_mul,
      _root_.NumberField.Chebotarev.frobeniusPrimePowerWeight_of_notMem hnot, _root_.Complex.ofReal_zero]











end NumberField.Chebotarev

end
end
