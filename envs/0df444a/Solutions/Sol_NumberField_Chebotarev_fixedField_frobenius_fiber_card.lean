-- Prove2me | solution 1 for NumberField.Chebotarev.fixedField_frobenius_fiber_card
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:47:56.970621+00:00
-- url     : https://prove2.me/submissions/86b2a724-20ec-4e70-bb2d-5f755cd5ece1

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_FieldTheory_Galois_FixedField
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_FrobeniusPrimeSet
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius_FiberCount
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.KrullTopology
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.DedekindDomain.Different
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.DedekindDomain.SelmerGroup
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.Tactic.Group
import Theorems.Thm_Ideal_eq_of_smul_eq_of_liesOver_under_fixedField
import Theorems.Thm_Ideal_frobenius_fiber_card_mul_orderOf_eq_card_centralizer
import Theorems.Thm_NumberField_Chebotarev_fixedField_frobenius_fiber_eq_image

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











/-- **The size of a conjugacy class is the index of the centralizer of any of its members.** The
class is the orbit of `g` under the conjugation action and the centralizer is the stabilizer, so
this is the orbit-stabilizer theorem. -/
theorem ncard_carrier_mk (g : G) :
    (ConjClasses.mk g).carrier.ncard = (Subgroup.centralizer {g}).index := by
  rw [← ConjAct.orbit_eq_carrier_conjClasses, ← MulAction.index_stabilizer,
    Subgroup.centralizer_eq_comap_stabilizer]
  exact ((MulAction.stabilizer (ConjAct G) g).index_comap_of_surjective
    (f := ConjAct.toConjAct.toMonoidHom) ConjAct.toConjAct.surjective).symm



/-- **The size of a conjugacy class is the index of the centralizer of any of its members**, in
`Nat.card` form.

Not `@[simp]`: Mathlib's `Nat.card_coe_set_eq` is itself `simp`, so the left-hand side simplifies
to `(ConjClasses.mk g).carrier.ncard` and the simp normal form linter rejects the pair; that
normalized form is `ConjClasses.ncard_carrier_mk`. -/
theorem card_carrier_mk (g : G) :
    Nat.card (ConjClasses.mk g).carrier = (Subgroup.centralizer {g}).index := by
  rw [Nat.card_coe_set_eq, ncard_carrier_mk]











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





/-- **That quotient in closed form.** Dividing the order of the group by the class size times the
order of a member leaves the order of the centralizer divided by that same order.

`hindex` is what lets the centralizer's index cancel from both sides; it holds automatically when
`G` is finite. The statement is an equality of `Nat.div` values, and no more: for a finite `G` both
divisions are exact and it reads as an equality of ratios, but `hindex` alone does not give that.
An infinite abelian group with an element of infinite order satisfies `hindex` while `Nat.card G`,
the centralizer's cardinality and `orderOf σ` are all `0`, and the identity is then `0 / 0`. -/
theorem card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf {G : Type*} [Group G]
    (C : ConjClasses G) (σ : G) (hσ : σ ∈ C.carrier)
    (hindex : (Subgroup.centralizer {σ}).index ≠ 0) :
    Nat.card G / (Nat.card C.carrier * orderOf σ)
      = Nat.card (Subgroup.centralizer {σ}) / orderOf σ := by
  rw [mem_carrier_iff_mk_eq] at hσ
  subst hσ
  rw [ConjClasses.card_carrier_mk, ← Subgroup.index_mul_card (Subgroup.centralizer {σ}),
    Nat.mul_div_mul_left _ _ (Nat.pos_of_ne_zero hindex)]



end ConjClasses

/-! ### Powers of a conjugacy class -/

namespace ConjClasses

variable {M : Type*} [Monoid M]























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
# The Artin symbol of an unramified prime

For a finite Galois extension of number fields, this file attaches to an unramified
prime ideal of the base the conjugacy class of its arithmetic Frobenius elements.
The definition uses Mathlib's `IsArithFrobAt` and `arithFrobAt`; no Frobenius
predicate or representative is introduced here.

The construction follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter I, §9,
Exercise 2.

The same reference gives functoriality in a normal tower: restriction maps the Artin symbol of
`L/K` to the Artin symbol of `M/K`. Unramifiedness in the intermediate extension is derived from
unramifiedness in the top extension, rather than assumed separately.

Raising the base field is the companion law, and it takes a power: for `K ⊆ M ⊆ L`, the symbol
of a prime of `𝓞 M` above `𝔭`, read inside `Gal(L/K)`, is the `f(𝔓/𝔭)`-th power of the symbol of
`𝔭`. Stated on conjugacy classes it names no prime of `𝓞 L` and no Frobenius representative, both
of which the element-level form in `TauCeti.NumberTheory.NumberField.Frobenius.Tower` fixes.

Finally, the symbol detects complete splitting: it is the identity class exactly when the
residue degree is one, equivalently when `𝓞 L` has `[L : K]` primes above `𝔭`.
-/

 section

open _root_.Ideal
open scoped _root_.NumberField _root_.Pointwise

namespace NumberField

variable {K : Type*} [Field K] [NumberField K]







/-- Every representative of `artinSymbol 𝔭 hur` is an arithmetic Frobenius at some prime above
`𝔭`. -/
theorem exists_isArithFrobAt_of_artinSymbol_eq_mk {L : Type*} [Field L] [NumberField L]
    [Algebra K L] [IsGalois K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      Algebra.IsUnramifiedAt (𝓞 K) Q) {σ : L ≃ₐ[K] L}
    (h : artinSymbol 𝔭 hur = ConjClasses.mk σ) :
    ∃ Q : 𝔭.primesOver (𝓞 L), IsArithFrobAt (𝓞 K) σ Q.1 := by
  obtain ⟨Q₀, _, _⟩ := (inferInstance : Nonempty (𝔭.primesOver (𝓞 L)))
  obtain ⟨σ₀, hσ₀⟩ := exists_isArithFrobAt K Q₀
    (Ideal.ne_bot_of_liesOver_of_ne_bot (NeZero.ne 𝔭) Q₀)
  have hconj : IsConj σ₀ σ := ConjClasses.mk_eq_mk_iff_isConj.mp
    ((artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur Q₀ σ₀ hσ₀).symm.trans h)
  obtain ⟨τ, hτ⟩ := isConj_iff.mp hconj
  exact ⟨Ideal.primesOver.mk 𝔭 (τ • Q₀), hτ ▸ hσ₀.conj τ⟩

section IsoOfExtensions

/-!
### Transport along an isomorphism of extensions

An isomorphism `e : L ≃ₐ[K] L'` of extensions of `K` induces `𝓞 L ≃ₐ[𝓞 K] 𝓞 L'`, and everything
`artinSymbol` is built from travels along it: the primes above `𝔭`, their unramifiedness, and the
Frobenius condition. The symbol itself is therefore equivariant for the induced isomorphism
`AlgEquiv.autCongr e` of Galois groups.
-/

variable {L L' : Type*} [Field L] [Algebra K L] [Field L'] [Algebra K L']

variable [NumberField L] [IsGalois K L] [NumberField L'] [IsGalois K L']



end IsoOfExtensions

section SplitsCompletely

/-!
### The trivial Artin symbol

Two equivalent readings of the identity Artin class at an unramified prime: residue degree one,
and complete splitting.
-/

variable {L : Type*} [Field L] [NumberField L] [Algebra K L] [IsGalois K L]





end SplitsCompletely

section BaseChange

/-!
### Raising the base field

The companion to `artinSymbol_map_restrictNormalHom`. That law shrinks the top field of a normal
tower and takes no power; this one raises the base field and takes the power `f(𝔓/𝔭)`.
-/

-- Source. Both transport laws are specified by `TauCetiRoadmap/Chebotarev/README.md` Layer 1,
-- which asks for closed transport lemmas derived from `artinSymbol_map_restrictNormalHom` and
-- `exists_isArithFrobAt_pow_inertiaDeg`. This is the second of the two.



end BaseChange

end NumberField

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
# The unramified primes carrying a prescribed Artin class

Let `L / K` be a finite Galois extension of number fields and let `C` be a conjugacy class in
`Gal(L/K)`. This file defines the set

`frobeniusPrimeSet K L C : Set (HeightOneSpectrum (𝓞 K))`

of height-one primes `𝔭` of `𝓞 K` that are unramified in `L` and whose Artin class is `C`. It is
the set whose density the Chebotarev density theorem computes.

## The dependent membership condition

`artinSymbol` is a *partial* construction: it takes an unramifiedness proof as an argument and has
no value at a ramified prime. So membership cannot be an equation between two total functions;
it is stated as

`∃ hur : (𝔭 is unramified in L), artinSymbol 𝔭.asIdeal hur = C`,

an existential over a proof. Membership is nonetheless unambiguous: it does not depend on which
unramifiedness proof witnesses it, and `mem_frobeniusPrimeSet_iff_artinSymbol_eq` turns the
existential into the plain equation `artinSymbol 𝔭.asIdeal hur = C` for whichever unramifiedness
proof `hur` the caller has in hand.

The alternative — a total `Gal(L/K)`-valued or `ConjClasses`-valued function taking a junk value
at the ramified primes — is worse for this set: the junk value carries no arithmetic content, yet
the ramified primes would sit inside the fibre of whichever class it names, so the fibres would
neither cover the unramified primes exactly nor be pinned down by a Frobenius element there. The
existential is what keeps the fibres free of them.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimeSet`: the primes of `𝓞 K` unramified in `L` whose Artin
  class is `C`.

## Main results

* `NumberField.Chebotarev.mem_frobeniusPrimeSet_iff_artinSymbol_eq`: proof-independence — with
  any unramifiedness proof in hand, membership is the equation `artinSymbol 𝔭.asIdeal hur = C`.
* `NumberField.Chebotarev.mem_frobeniusPrimeSet_mk_iff_exists_isArithFrobAt`: for an unramified
  `𝔭` and an element `σ`, membership in the fibre of `[σ]` says exactly that `σ` is an arithmetic
  Frobenius at *some* prime of `𝓞 L` above `𝔭`.
* `NumberField.Chebotarev.frobeniusPrimeSet_map_autCongr`: equivariance — an isomorphism
  `e : L ≃ₐ[K] L'` of extensions of `K` matches the fibre of `C` in `L` with the fibre in `L'` of
  the image of `C` under the induced isomorphism `AlgEquiv.autCongr e` of Galois groups.
* `NumberField.Chebotarev.frobeniusPrimeSet_subset_map_restrictNormalHom`: a fibre over `L` lies
  in the fibre over a Galois subextension `M` of the restricted class.
* `NumberField.Chebotarev.disjoint_frobeniusPrimeSet`: distinct classes have disjoint fibres.
* `NumberField.Chebotarev.iUnion_frobeniusPrimeSet`: the fibres cover exactly the complement of
  `ramifiedPrimes K L`, so `existsUnique_mem_frobeniusPrimeSet` partitions the unramified primes
  and `finite_compl_iUnion_frobeniusPrimeSet` records that the discarded remainder is finite.

The last two are what let the density arguments discard a finite exceptional set and then work
one class at a time: a lower density bound for each class can be squeezed against a partition of
a cofinite set, which is how the crossing argument produces exact densities.
-/

 section

open _root_.Ideal
open scoped _root_.NumberField

open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]



/-- Membership in `frobeniusPrimeSet`, unfolded. Downstream files should open the definition
through this lemma rather than through defeq. -/
@[simp]
theorem mem_frobeniusPrimeSet_iff {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} :
    𝔭 ∈ frobeniusPrimeSet K L C ↔
      ∃ hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q, artinSymbol 𝔭.asIdeal hur = C :=
  Iff.rfl







/-- A member of `frobeniusPrimeSet K L C` is unramified in `L`. -/
theorem isUnramifiedAt_of_mem_frobeniusPrimeSet {𝔭 : HeightOneSpectrum (𝓞 K)}
    {C : ConjClasses (L ≃ₐ[K] L)} (h : 𝔭 ∈ frobeniusPrimeSet K L C)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭.asIdeal] :
    Algebra.IsUnramifiedAt (𝓞 K) Q :=
  (mem_frobeniusPrimeSet_iff.mp h).elim fun hur _ ↦ hur Q





/-- **Every representative is realized.** If `𝔭` lies in the fibre of the class of `σ`, then `σ`
itself — not merely some conjugate of it — is an arithmetic Frobenius at some prime of `𝓞 L`
above `𝔭`. -/
theorem exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk {𝔭 : HeightOneSpectrum (𝓞 K)}
    {σ : L ≃ₐ[K] L} (h : 𝔭 ∈ frobeniusPrimeSet K L (ConjClasses.mk σ)) :
    ∃ Q : 𝔭.asIdeal.primesOver (𝓞 L), IsArithFrobAt (𝓞 K) σ Q.1 := by
  obtain ⟨hur, hC⟩ := mem_frobeniusPrimeSet_iff.mp h
  exact exists_isArithFrobAt_of_artinSymbol_eq_mk 𝔭.asIdeal hur hC



section IsoOfExtensions

variable {L' : Type*} [Field L'] [NumberField L'] [Algebra K L'] [IsGalois K L']



end IsoOfExtensions

section RestrictNormal

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L] [IsScalarTower K M L]
  [IsGalois K M]



end RestrictNormal











end NumberField.Chebotarev

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
# How many primes carry a given Frobenius element

Let `L / K` be a finite Galois extension of number fields, `𝔭` an ideal of `𝓞 K` and `σ` an
element of `Gal(L/K)`. The primes of `𝓞 L` above `𝔭` at which `σ` is an arithmetic Frobenius form
the *fiber* of `σ`, and `Ideal.frobenius_fiber_card_eq_of_isConj` shows that conjugate elements
have fibers of the same size. This file computes that size, at a prime where `σ` is a Frobenius
and `L / K` is unramified:

```text
#(fiber of σ) * orderOf σ = #Centralizer_{Gal(L/K)}(σ)
```

The reason is that the fiber is a single orbit. `Gal(L/K)` acts transitively on the primes above
`𝔭`, and the Frobenius at `τ • Q` is `τ σ τ⁻¹`, so the elements carrying `Q` to another member of
the fiber are exactly those commuting with `σ`. The stabilizer of `Q` inside that centralizer is
the decomposition group `⟨σ⟩`, whose order is `orderOf σ`, and the orbit-stabilizer theorem gives
the count.

The identity is stated as a product rather than as `#Centralizer(σ) / orderOf σ` so that it says
something without a separate divisibility: `orderOf σ` divides the centralizer's order because
`⟨σ⟩` is a subgroup of it, and `ConjClasses.card_carrier_mul_orderOf_dvd` records the companion
divisibility for a whole conjugacy class.

## Main results

* `Ideal.frobenius_fiber_eq_orbit_centralizer`: the fiber of `σ` above `𝔭` is the orbit of any of
  its members under the centralizer of `σ`.
* `Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer`: its size, times `orderOf σ`, is
  the order of that centralizer.
* `HeightOneSpectrum.frobeniusFiberEquiv`: the height-one-prime and ideal representations of the
  fiber are equivalent.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open scoped NumberField Pointwise
open IsDedekindDomain (HeightOneSpectrum)

namespace Ideal

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

-- Source. The count is specified by the Chebotarev roadmap:
-- `TauCetiRoadmap/Chebotarev/README.md` §8.2, which displays the fibre size as
-- `#G / (#C * f) = #Centralizer_G(σ) / f` with `f = orderOf σ`. The theorems below count the
-- primes of `𝓞 L`; the roadmap's own statement counts primes of the fixed field `L ^ ⟨σ⟩`, and
-- reaches this one through the residue degree of a fixed-field prime.





end Ideal

namespace IsDedekindDomain.HeightOneSpectrum

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]







/-- **The absolute Frobenius fibre, counted.** The primes of `L` over `p` at which `σ` is an
arithmetic Frobenius form a single orbit of the centralizer of `σ`, whose stabilizer is `⟨σ⟩`, so
there are `#Centralizer(σ) / orderOf σ` of them.

This is `Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer` solved for the fibre and
re-indexed: that theorem states the product and is indexed by ideals lying over `p.asIdeal`, while
counting arguments over a number field index by `HeightOneSpectrum` primes contracting to `p`.
`HeightOneSpectrum.frobeniusFiberEquiv` bridges the two indexings, and the division is exact
because `orderOf σ` is the size of a stabilizer inside the acting group. -/
theorem frobenius_fiber_card_eq_card_centralizer_div_orderOf (p : HeightOneSpectrum (𝓞 K))
    {σ : L ≃ₐ[K] L} (Q : Ideal (𝓞 L)) [IsGalois K L] [Q.IsPrime] [Q.LiesOver p.asIdeal]
    [Algebra.IsUnramifiedAt (𝓞 K) Q] (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    Nat.card {R : HeightOneSpectrum (𝓞 L) //
        R.under (𝓞 K) = p ∧ IsArithFrobAt (𝓞 K) σ R.asIdeal} =
      Nat.card (Subgroup.centralizer {σ}) / orderOf σ :=
  (Nat.card_congr (p.frobeniusFiberEquiv σ)).trans <|
    Nat.eq_div_of_mul_eq_left (orderOf_pos σ).ne'
      (Ideal.frobenius_fiber_card_mul_orderOf_eq_card_centralizer p.asIdeal Q hσ)

end IsDedekindDomain.HeightOneSpectrum

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
# Frobenius fibers over cyclic fixed fields

Let `L / K` be a finite Galois extension, let `C` be a conjugacy class in `Gal(L/K)`, and choose
`sigma` in `C`.  Put `E = L ^ <sigma>`.  This file counts the primes of `E` over a prime in the
Frobenius class `C` whose relative Frobenius in `L / E` is the automorphism induced by `sigma`:

```text
#G / (#C * orderOf sigma).
```

Contraction identifies these primes with the primes of `L` at which `sigma` itself is an
arithmetic Frobenius.  The latter form one orbit under the centralizer of `sigma`; its stabilizer
is `<sigma>`.  The resulting count is the fixed-field multiplicity used when transferring prime
sums and densities between `E` and `K`.

## Main result

* `NumberField.Chebotarev.fixedField_frobenius_fiber_eq_image`: contraction identifies the
  relative fiber with the image of the corresponding absolute Frobenius fiber.
* `NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet`: away from the
  ramified primes, a prime of the relative fiber has residue degree one over `K` exactly when the
  prime below it lies in the Frobenius fiber of `sigma`.
* `NumberField.Chebotarev.fixedField_frobenius_fiber_card`: the exact cardinality of the relative
  Frobenius fiber over one prime of `K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter I, Section 9.
* R. Sharifi, *Algebraic Number Theory*, Theorem 7.2.2.
* C. Birkbeck and R. Brasca,
  [*Chebotarev density*](https://github.com/CBirkbeck/chebotarev-density),
  `CebotarevDensity/FixedFieldDensity.lean` at commit
  `55a89985d47a3befcf6069aca1da250ff088b5c7` (Apache-2.0).
-/

 section

open IntermediateField
open scoped NumberField Pointwise
open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]











omit [_root_.IsGalois K L] in
private theorem NumberField.Chebotarev.under_fixedField_injOn_frobenius
    (sigma : L ≃ₐ[K] L) (p : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    _root_.Set.InjOn (fun Q : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 L) ↦
      Q.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma))))
      {Q : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 L) |
        Q.under (𝓞 K) = p ∧ _root_.IsArithFrobAt (𝓞 K) sigma Q.asIdeal} := by
  intro Q hQ R hR hQR
  apply _root_.IsDedekindDomain.HeightOneSpectrum.ext
  let _ : R.asIdeal.LiesOver
      (Q.asIdeal.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)))) :=
    ⟨_root_.congrArg _root_.IsDedekindDomain.HeightOneSpectrum.asIdeal hQR⟩
  exact (_root_.Ideal.eq_of_smul_eq_of_liesOver_under_fixedField
    hQ.2.mem_stabilizer R.asIdeal).symm

-- The counting argument follows Birkbeck--Brasca, `CebotarevDensity/FixedFieldDensity.lean`.
/-- **The fixed-field Frobenius fiber count.** Let `sigma` represent the conjugacy class `C`, and
let `p` be an unramified prime with Artin class `C`.  The number of primes of
`L ^ <sigma>` above `p` whose relative Artin class in `L / L ^ <sigma>` is represented by
`sigma.toFixedFieldAlgEquiv` is

```text
#Gal(L/K) / (#C * orderOf sigma).
```

The division is exact by `ConjClasses.card_carrier_mul_orderOf_dvd`. -/
theorem solution
    (C : _root_.ConjClasses (L ≃ₐ[K] L)) (sigma : L ≃ₐ[K] L) (hsigma : sigma ∈ C.carrier)
    (p : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (hp : p ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet K L C) :
    _root_.Nat.card {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma))) //
      P.under (𝓞 K) = p ∧
        P ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
          (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv)} =
      _root_.Nat.card (L ≃ₐ[K] L) / (_root_.Nat.card C.carrier * _root_.orderOf sigma) := by
  have hC : _root_.ConjClasses.mk sigma = C := ConjClasses.mem_carrier_iff_mk_eq.mp hsigma
  have hp' : p ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet K L (_root_.ConjClasses.mk sigma) := hC ▸ hp
  obtain ⟨Q, hQ⟩ := _root_.NumberField.Chebotarev.exists_isArithFrobAt_of_mem_frobeniusPrimeSet_mk hp'
  have : _root_.Algebra.IsUnramifiedAt (𝓞 K) Q.1 := _root_.NumberField.Chebotarev.isUnramifiedAt_of_mem_frobeniusPrimeSet hp' Q.1
  let lowerFiber : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)))) :=
    {P | P.under (𝓞 K) = p ∧
      P ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
        (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv)}
  let upperFiber : _root_.Set (_root_.IsDedekindDomain.HeightOneSpectrum (𝓞 L)) :=
    {R | R.under (𝓞 K) = p ∧ _root_.IsArithFrobAt (𝓞 K) sigma R.asIdeal}
  have himage : lowerFiber =
      (fun R : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 L) ↦
        R.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)))) '' upperFiber :=
    _root_.NumberField.Chebotarev.fixedField_frobenius_fiber_eq_image sigma p hp'
  have hinj := _root_.NumberField.Chebotarev.under_fixedField_injOn_frobenius sigma p
  calc
    _root_.Nat.card {P : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma))) //
        P.under (𝓞 K) = p ∧
          P ∈ _root_.NumberField.Chebotarev.frobeniusPrimeSet ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
            (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv)}
        = _root_.Nat.card lowerFiber := _root_.rfl
    _ = _root_.Nat.card ((fun R : _root_.IsDedekindDomain.HeightOneSpectrum (𝓞 L) ↦
          R.under (𝓞 ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)))) '' upperFiber) := by rw [himage]
    _ = _root_.Nat.card upperFiber :=
      _root_.Nat.card_congr hinj.bijOn_image.equiv.symm
    _ = _root_.Nat.card (_root_.Subgroup.centralizer {sigma}) / _root_.orderOf sigma :=
      p.frobenius_fiber_card_eq_card_centralizer_div_orderOf Q.1 hQ
    _ = _root_.Nat.card (L ≃ₐ[K] L) / (_root_.Nat.card C.carrier * _root_.orderOf sigma) := by
      rw [← C.card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf sigma hsigma]
      exact _root_.Subgroup.index_ne_zero_of_finite

end NumberField.Chebotarev

end
end
