-- Prove2me | solution 1 for NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:17:10.745296+00:00
-- url     : https://prove2.me/submissions/78ce4083-a47c-41ee-9bcb-52cd0f48aeda

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.KummerPolynomial
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.Ideal.Over
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Unramified.Locus

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Frobenius elements for a group acting on a ring extension

This file supplements Mathlib's `IsArithFrobAt` API with facts about a monoid or group acting on
a commutative ring extension `S/R`. All of them are stated at ring level, so they are available
independently of any number-field or Legendre-symbol specialization.

Two are properties of a single Frobenius element. The defining congruence has `#(R ⧸ Q ∩ R)` as
its exponent, so it makes that residue ring finite and therefore forces `Q ≠ ⊥` over an infinite
base. Iterating it `n` times replaces the exponent by its `n`-th power, which is what a Frobenius
over an intermediate ring of residue degree `n` is required to satisfy.

For an ideal `p` of `R`, an element `σ` of the acting group cuts out the set of primes of `S` above
`p` that admit `σ` as an arithmetic Frobenius. These sets need not be disjoint: at a ramified prime
several elements are a Frobenius at once, so this is a family of fibers rather than a partition.
Disjointness at a prime `Q` is what `IsArithFrobAt.eq_of_isUnramifiedAt` below supplies, under
hypotheses of its own: a faithful action, `S` Noetherian, `Q.primeCompl ≤ S⁰`, and
`Algebra.IsUnramifiedAt R Q`. Exhaustion of the primes above `p` needs a Frobenius to exist at
each of them, which again carries hypotheses of its own, such as those of
`IsArithFrobAt.exists_of_isInvariant`.

## Main results

* `IsArithFrobAt.eq_of_isUnramifiedAt` — a Frobenius element is unique for a faithful action at an
  unramified prime of a Noetherian ring whose prime complement consists of non-zero-divisors.
* `IsArithFrobAt.ne_bot` — a prime carrying a Frobenius element over an infinite base ring is
  nonzero.
* `IsArithFrobAt.mk_pow_smul` — the `n`-th power of a Frobenius element acts on the residue ring
  by the `q ^ n`-th power map.
* `Ideal.nonempty_frobenius_fiber_equiv_of_isConj` — conjugate elements have equipotent fibers
  above a fixed ideal of the base, as a bijection between them.
* `Ideal.frobenius_fiber_card_eq_of_isConj` — the `Nat.card` form of that equipotence.

The equipotence is the "distributed evenly" step of Chebotarev's density theorem: where the fibers
do partition the primes above `p`, it is what lets a count over a whole conjugacy class be
recovered from the count at a single representative. Because `S` is an arbitrary commutative ring
the fibers may be infinite, and `Nat.card` is `0` on an infinite type; the bijection is therefore
the primary statement and the `Nat.card` identity is derived from it.

## Implementation notes

The bijection realizing the equipotence is not conjugation itself but the pointwise action
`P ↦ c • P` of a witnessing element `c`; Mathlib's `IsArithFrobAt.conj` is what transports the
Frobenius condition along it, sending a Frobenius `σ` at `P` to the Frobenius `c * σ * c⁻¹` at
`c • P`.

The source states the equipotence for the rings of integers of a Galois extension of number
fields and under an unramifiedness hypothesis on `p` that it never uses. Both restrictions are
dropped here: the transport argument uses only the generic Frobenius group-action API, and it is
available at every prime.

## References

* Sharifi, *Algebraic Number Theory*, Theorem 7.2.2 (p. 143).
* Stevenhagen–Lenstra, *Chebotarëv and his density theorem*, Appendix.
* Birkbeck–Brasca, [chebotarev-density](https://github.com/CBirkbeck/chebotarev-density)
  (Apache-2.0), commit `8575c9df1ae0a61120ab5c964c7911414254bec7`, file
  `CebotarevDensity/FixedFieldDensity.lean`, declaration `frobeniusFibre_card_eq_of_isConj`
  (source line 54). The transport argument of `nonempty_frobenius_fiber_equiv_of_isConj` below,
  and the statement of the `frobenius_fiber_card_eq_of_isConj` derived from it, are adapted from
  that declaration; the source states only the `Nat.card` form.
-/

 section

open nonZeroDivisors

open scoped Pointwise

namespace Ideal



/-- **A prime carrying an arithmetic Frobenius over an infinite base is nonzero.** The defining
congruence has the cardinality of `R ⧸ Q ∩ R` as its exponent, so it forces that residue ring to
be finite; over an infinite `R` this rules out `Q = ⊥`. -/
theorem _root_.IsArithFrobAt.ne_bot {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [FaithfulSMul R S] [Infinite R] [Monoid G] [MulSemiringAction G S] [SMulCommClass G R S]
    {Q : Ideal S} {σ : G} (H : _root_.IsArithFrobAt R σ Q) : Q ≠ ⊥ := by
  rintro rfl
  have hfin : Finite (R ⧸ Ideal.under R (⊥ : Ideal S)) := H.finite_quotient
  rw [Ideal.under_bot] at hfin
  have : Finite R := Finite.of_equiv _ (RingEquiv.quotientBot R).toEquiv
  exact not_finite R



variable {R S G : Type*} [CommRing R] [CommRing S] [Algebra R S] [Group G]
  [MulSemiringAction G S] [SMulCommClass G R S]







end Ideal

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
# Raising the base field: the tower formula for arithmetic Frobenius elements

Let `K ⊆ M ⊆ L` be number fields with `L / K` and `L / M` Galois, let `Q` be a prime of `𝓞 L`
unramified over `𝓞 K`, and write `𝔓 = Q ∩ 𝓞 M` and `𝔭 = Q ∩ 𝓞 K`. An arithmetic Frobenius
`σ ∈ Gal(L/K)` at `Q` acts on the residue field by `x ↦ x ^ 𝔑𝔭`, while an arithmetic Frobenius
`τ ∈ Gal(L/M)` at `Q` acts by `x ↦ x ^ 𝔑𝔓`. Since `𝔑𝔓 = 𝔑𝔭 ^ f(𝔓/𝔭)`, the two are related by

```text
AlgEquiv.restrictScalars K τ = σ ^ f(𝔓/𝔭).
```

The exponent is a **power**, the residue degree of the intermediate prime over the base, and never
an inverse. In particular `σ ^ f(𝔓/𝔭)` fixes `M` pointwise even though `M / K` need not be normal
and `σ` itself need not preserve `M`.

This is the second of the two tower laws for Frobenius elements. The first, restriction along a
normal subextension, takes no power at all and is
`IsArithFrobAt.restrictNormal` in `TauCeti.NumberTheory.NumberField.Frobenius.Restriction`.

## The two hypotheses that are not decoration

The statement is *relative to one prime `Q` of `L`*. Replacing `σ` by an arbitrary conjugate — an
arbitrary representative of the Artin class of `𝔭` — makes it false when `M / K` is not normal: a
conjugate need not stabilize `Q`, so its `f`-th power need not fix `M` pointwise, and it is then
the restriction of no element of `Gal(L/M)` at all.

Unramifiedness of `Q` over `𝓞 K` is likewise essential. At a ramified prime a Frobenius lift is
determined only modulo inertia, so there is no equality of automorphisms to prove; the statement
would have to be made in the quotient by the inertia subgroup, or about a coset. Here
unramifiedness enters through `Ideal.stabilizerHom_injective_of_isUnramifiedAt`: the decomposition
group of `Q` embeds into the automorphism group of the residue extension, so an element of
`Gal(L/K)` stabilizing `Q` is pinned down by its residue action, and both `σ ^ f(𝔓/𝔭)` and
`AlgEquiv.restrictScalars K τ` act by `x ↦ x ^ 𝔑𝔓`.

## Main results

* `NumberField.restrictScalars_eq_pow_inertiaDeg`: an arithmetic Frobenius of `Gal(L/M)` at `Q`
  restricts to the `f(𝔓/𝔭)`-th power of an arithmetic Frobenius of `Gal(L/K)` at `Q`.
* `NumberField.isArithFrobAt_iff_restrictScalars_eq_pow_inertiaDeg`: that power characterizes the
  relative Frobenius among the elements of `Gal(L/M)` after restriction to `Gal(L/K)`.
* `NumberField.restrictScalars_arithFrobAt_eq_pow_inertiaDeg`: the same formula for Mathlib's
  coherently chosen `arithFrobAt`, which is what the Artin symbol is built from.
* `NumberField.exists_isArithFrobAt_pow_inertiaDeg`: the existence form of the tower formula,
  stated for prime ideals `𝔓` and `𝔭` presented by their defining equations.
* `NumberField.pow_inertiaDeg_apply_algebraMap`: the `f(𝔓/𝔭)`-th power of `σ` fixes `M`
  pointwise.
* `NumberField.restrictScalars_eq_of_inertiaDeg_eq_one`: at residue degree one the restriction
  of the relative Frobenius is `σ` itself, with no power.
* `NumberField.isArithFrobAt_restrictScalars_of_inertiaDeg_eq_one`: the same at residue degree
  one, concluding that the restriction is an arithmetic Frobenius rather than assuming one.
* `NumberField.isArithFrobAt_int_of_absNorm_eq`: a relative Frobenius above an ideal of absolute
  norm `p` is also a Frobenius over the ideal `(p)` of `ℤ`.
* `NumberField.isArithFrobAt_one_of_pow_eq_one` and
  `NumberField.isArithFrobAt_eq_one_of_pow_eq_one`: when an absolute Frobenius at `Q` has order
  dividing `n` and the residue field of `Q ∩ 𝓞 M` has `p ^ n` elements, the relative Frobenius
  of `Gal(L/M)` at `Q` is the identity.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter I, §9.
-/

 section

open Ideal

open scoped NumberField Pointwise

namespace NumberField
end NumberField
section NumberField
open NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L] {M : Type*} [Field M] [NumberField M] [Algebra K M] [Algebra M L]
  [IsScalarTower K M L] {Q : Ideal (𝓞 L)} [Q.IsPrime]















omit [_root_.IsGalois K L] in
/-- **A relative Frobenius at residue degree one restricts to an absolute one.**  If `Q ∩ 𝓞 M`
has residue degree one over `𝓞 K`, then the restriction to `Gal(L/K)` of an arithmetic Frobenius
of `Gal(L/M)` at `Q` is itself an arithmetic Frobenius at `Q` over `𝓞 K`.

Residue degree one says the two residue fields have the same size, and restricting scalars does
not move the automorphism, so the two Frobenius conditions are the same condition. Neither
`L / K` Galois nor `Q` unramified is needed: this is a statement about `Q` alone. -/
theorem solution
    {τ : L ≃ₐ[M] L} (hτ : _root_.IsArithFrobAt (𝓞 M) τ Q)
    (hf : (Q.under (𝓞 M)).inertiaDeg (𝓞 K) = 1) :
    _root_.IsArithFrobAt (𝓞 K) (_root_.AlgEquiv.restrictScalars K τ) Q := by
  have _ : Q.IsMaximal := _root_.Ring.DimensionLEOne.maximalOfPrime hτ.ne_bot _root_.inferInstance
  have _ : (Q.under (𝓞 M)).IsMaximal := _root_.Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  have _ : (Q.under (𝓞 K)).IsMaximal := _root_.Ideal.isMaximal_comap_of_isIntegral_of_isMaximal Q
  have _ : (Q.under (𝓞 M)).LiesOver (Q.under (𝓞 K)) := ⟨by rw [_root_.Ideal.under_under]⟩
  -- At residue degree one the `𝓞 M`-residue field and the `𝓞 K`-residue field have equal size.
  have hcard : _root_.Nat.card (𝓞 M ⧸ Q.under (𝓞 M)) = _root_.Nat.card (𝓞 K ⧸ Q.under (𝓞 K)) := by
    have := _root_.Ideal.cardQuot_pow_inertiaDeg (R := 𝓞 K) (S := 𝓞 M)
      (Q.under (𝓞 K)) (Q.under (𝓞 M))
    simpa [_root_.Submodule.cardQuot_apply, hf] using this.symm
  intro x
  -- `AlgEquiv.restrictScalars` leaves the action on `𝓞 L` alone, so only the exponents differ.
  exact hcard ▸ hτ x

/-! ### Trivial relative Frobenius elements

A prime that is already inert enough over `ℚ` has trivial relative Frobenius: if the absolute
Frobenius `ρ` at `Q` has `ρ ^ n = 1` and the residue field of `Q ∩ 𝓞 M` has `p ^ n` elements, then
the residue action of the relative Frobenius, raising to the power `p ^ n`, is the identity.
-/





end NumberField

end
end
