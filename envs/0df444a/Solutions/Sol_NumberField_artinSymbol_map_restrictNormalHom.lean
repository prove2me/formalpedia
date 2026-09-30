-- Prove2me | solution 1 for NumberField.artinSymbol_map_restrictNormalHom
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:29:01.925134+00:00
-- url     : https://prove2.me/submissions/8beb25e4-37a6-4978-a74e-3f05efff66f9

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_NumberTheory_NumberField_Frobenius
import Definitions.Def_TauCeti_NumberTheory_RamificationInertia_Tower
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Unramified.Locus
import Theorems.Thm_NumberField_algebraMap_restrictNormal_smul

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















/-- The image of the class of `a` under `ConjClasses.map f` is the class of `f a`. -/
-- Mathlib defines `ConjClasses.map` as a `Quotient.lift` and provides no computation rule for it,
-- so this reduction is stated here once and every naturality statement below rewrites with it.
@[simp]
theorem map_mk {N : Type*} [Monoid N] (f : M →* N) (a : M) :
    ConjClasses.map f (ConjClasses.mk a) = ConjClasses.mk (f a) := rfl







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
# Restriction of arithmetic Frobenius

An arithmetic Frobenius in a field extension remains an arithmetic Frobenius after restriction
to a normal intermediate extension. More precisely, if `L/M/K` is a tower with `M/K` normal and
`σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`, then `σ|_M` is an arithmetic Frobenius at the
contracted prime `Q ∩ 𝓞 M`.

This is the unpowered restriction law: both Frobenius elements are relative to the same base
field `K`, so both act on residue fields by the cardinality of the residue field of the same base
prime. The distinct tower law obtained by raising the base from `K` to `M` involves the inertia
degree as an exponent and is not proved here.

The argument follows Jürgen Neukirch, *Algebraic Number Theory*, Chapter I, §9.

## Main result

* `IsArithFrobAt.restrictNormal`: restriction to a normal intermediate extension preserves the
  arithmetic-Frobenius property at the contracted prime.
-/

 section

open Ideal
open scoped NumberField

namespace IsArithFrobAt

variable {K M L : Type*} [Field K] [Field M] [Field L] [Algebra K M] [Algebra M L]
  [Algebra K L] [IsScalarTower K M L] [Normal K M]

/-- **Arithmetic Frobenius restricts without a power along a normal subextension.**

If `σ ∈ Gal(L/K)` is an arithmetic Frobenius at `Q`, its restriction to a normal intermediate
extension `M/K` is an arithmetic Frobenius at `Q ∩ 𝓞 M`. The exponent on both sides is the
cardinality of `𝓞 K` modulo the contraction of `Q`; `Ideal.under_under` identifies the two
contractions. -/
theorem restrictNormal {Q : Ideal (𝓞 L)} {σ : L ≃ₐ[K] L}
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    IsArithFrobAt (𝓞 K) (σ.restrictNormal M) (Q.under (𝓞 M)) := by
  intro x
  rw [Ideal.mem_under, MulSemiringAction.toAlgHom_apply, map_sub,
    NumberField.algebraMap_restrictNormal_smul, map_pow, Ideal.under_under]
  exact hσ (algebraMap (𝓞 M) (𝓞 L) x)

end IsArithFrobAt

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
end NumberField
section NumberField
open NumberField

variable {K : Type*} [Field K] [NumberField K]





/-- **The Artin symbol is functorial under restriction to a normal subextension.** For a normal
tower `L/M/K`, applying restriction to the conjugacy class `artinSymbol 𝔭` for `L/K` gives the
Artin symbol for `M/K`. The latter's unramifiedness witness is derived canonically from the
hypothesis for `L/K`. -/
theorem solution {M L : Type*} [_root_.Field M] [_root_.NumberField M]
    [_root_.Field L] [_root_.NumberField L] [_root_.Algebra K M] [_root_.Algebra M L] [_root_.Algebra K L]
    [_root_.IsScalarTower K M L] [_root_.IsGalois K L] [_root_.IsGalois K M]
    (𝔭 : _root_.Ideal (𝓞 K)) [𝔭.IsMaximal]
    (hur : ∀ (Q : _root_.Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver 𝔭],
      _root_.Algebra.IsUnramifiedAt (𝓞 K) Q) :
    _root_.ConjClasses.map (_root_.AlgEquiv.restrictNormalHom (F := K) (K₁ := L) M)
        (_root_.NumberField.artinSymbol 𝔭 hur) =
      _root_.NumberField.artinSymbol 𝔭 (fun P _ _ ↦
        _root_.TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn (S := 𝓞 L)
          (fun Q hQ hQ' ↦ @hur Q hQ hQ') P) := by
  let Q : 𝔭.primesOver (𝓞 L) := _root_.Classical.choice _root_.inferInstance
  let _ : Q.1.IsPrime := Q.2.1
  let _ : Q.1.LiesOver 𝔭 := Q.2.2
  have h𝔭ne : 𝔭 ≠ ⊥ :=
    (𝔭.bot_lt_of_maximal (_root_.NumberField.RingOfIntegers.not_isField K)).ne'
  obtain ⟨σ, hσ⟩ := _root_.NumberField.exists_isArithFrobAt K Q.1
    (_root_.Ideal.ne_bot_of_liesOver_of_ne_bot h𝔭ne Q.1)
  rw [_root_.NumberField.artinSymbol_eq_mk_of_isArithFrobAt 𝔭 hur Q.1 σ hσ,
    _root_.NumberField.artinSymbol_eq_mk_of_isArithFrobAt 𝔭
      (fun P _ _ ↦
        _root_.TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn (S := 𝓞 L)
          (fun Q hQ hQ' ↦ @hur Q hQ hQ') P)
      (Q.1.under (𝓞 M))
      (σ.restrictNormal M) hσ.restrictNormal]
  -- `AlgEquiv.restrictNormalHom M σ` is `σ.restrictNormal M`, so this is exactly the computation
  -- rule for `ConjClasses.map` on representatives.
  exact _root_.ConjClasses.map_mk _ σ



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
