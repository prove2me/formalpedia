-- Prove2me | solution 1 for NumberField.Chebotarev.frobeniusPsi_fixedField_asymptotic_iff
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T22:13:41.868147+00:00
-- url     : https://prove2.me/submissions/51f6aac1-e902-4b2a-b895-f685e9f147d2

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_Algebra_Group_Conj
import Definitions.Def_TauCeti_FieldTheory_Galois_FixedField
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Counting
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Prime_Psi
import Definitions.Def_TauCeti_NumberTheory_ArithmeticDirichletSeries_Weight
import Definitions.Def_TauCeti_NumberTheory_Chebotarev_PrimeCounting_VonMangoldt
import Definitions.Def_TauCeti_NumberTheory_NumberField_ArtinSymbol
import Definitions.Def_TauCeti_NumberTheory_NumberField_AutomorphismAction
import Definitions.Def_TauCeti_Order_Northcott_Basic
import Mathlib.Algebra.Algebra.Subalgebra.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharP.Basic
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Group.ConjFinite
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Ring.Subgroup
import Mathlib.Algebra.Ring.Subring.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Set.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.QuotientGroup
import Mathlib.Data.ZMod.Units
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
import Mathlib.LinearAlgebra.Pi
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.NumberTheory.ArithmeticFunction.LFunction
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.NumberTheory.NumberField.DedekindZeta
import Mathlib.NumberTheory.NumberField.DirichletDensity
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.Ideal.Basic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.NumberTheory.RamificationInertia.Inertia
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Order.Filter.AtTopBot.Finset
import Mathlib.Order.Northcott
import Mathlib.RingTheory.ClassGroup.Basic
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
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.RingTheory.UniqueFactorizationDomain.Finite
import Mathlib.RingTheory.Unramified.Locus
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic.Group
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Topology.UniformSpace.Real
import Theorems.Thm_NumberField_Chebotarev_frobeniusPsi_fixedField_sub_mul_frobeniusPsi_isLittleO

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

/-- **The size of a conjugacy class times the order of a member divides the order of the group.**

For a *finite* group this is what makes `Nat.card G / (Nat.card C.carrier * orderOf σ)` an exact
ratio rather than a truncated division, which
`card_div_card_carrier_mul_orderOf_eq_card_centralizer_div_orderOf` then evaluates. No finiteness
is assumed here: for an infinite group `Nat.card G` is `0`, and every natural number divides `0`. -/
theorem card_carrier_mul_orderOf_dvd {G : Type*} [Group G] (C : ConjClasses G) (σ : G)
    (hσ : σ ∈ C.carrier) :
    Nat.card C.carrier * orderOf σ ∣ Nat.card G := by
  rw [mem_carrier_iff_mk_eq] at hσ
  subst hσ
  obtain ⟨k, hk⟩ := (Subgroup.centralizer {σ}).orderOf_dvd_natCard
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  exact ⟨k, by rw [ConjClasses.card_carrier_mk, mul_assoc, ← hk, Subgroup.index_mul_card]⟩

/-- **That quotient is positive.** For a finite group the class size times the order of a member
divides the group order and both are positive, so the ratio `Nat.card G / (#C.carrier * orderOf σ)`
is a positive natural number rather than a truncation to zero.

Finiteness is needed, and not only for convenience: for an infinite `G` every one of
`Nat.card G`, `Nat.card C.carrier` and `orderOf σ` may be `0`, and the quotient is then `0 / 0`. -/
theorem card_div_card_carrier_mul_orderOf_pos {G : Type*} [Group G] [Finite G]
    (C : ConjClasses G) (σ : G) (hσ : σ ∈ C.carrier) :
    0 < Nat.card G / (Nat.card C.carrier * orderOf σ) :=
  have : Nonempty C.carrier := ⟨⟨σ, hσ⟩⟩
  Nat.div_pos (Nat.le_of_dvd Nat.card_pos (C.card_carrier_mul_orderOf_dvd σ hσ))
    (Nat.mul_pos Nat.card_pos (orderOf_pos σ))





end ConjClasses

/-! ### Powers of a conjugacy class -/

namespace ConjClasses

variable {M : Type*} [Monoid M]























end ConjClasses

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
# Contracting Frobenius `ϑ` and `ψ` from a cyclic fixed field

Let `L / K` be a finite Galois extension of number fields, let `C` be a conjugacy class of
`Gal(L/K)`, choose `sigma ∈ C`, and put `E = L ^ <sigma>`.  This file proves the exact identity

```text
∑_{𝔓 ∈ S_E, N 𝔓 ≤ x} log N 𝔓 = (#G / (#C * orderOf sigma)) * ϑ_C(x),
```

where `S_E` is the set of primes `𝔓` of `E` whose relative Artin class in `L / E` is represented by
`sigma`, that do not lie above `ramifiedPrimes K L`, and that have residue degree one over `K`.

There is no error term.  Away from the ramified primes, a prime `𝔓` of the relative fibre has
residue degree one over `K` exactly when the prime `𝔭` of `K` below it lies in the Frobenius fibre
of `C` (`NumberField.Chebotarev.inertiaDeg_eq_one_iff_under_mem_frobeniusPrimeSet`); then
`N 𝔓 = N 𝔭`, and over each such `𝔭` there are exactly `#G / (#C * orderOf sigma)` of them
(`NumberField.Chebotarev.fixedField_frobenius_fiber_card`).

The identity concerns `ϑ` at residue degree one only.  The other primes of the relative fibre have
residue degree at least two over `ℚ` or lie above `ramifiedPrimes K L`, so they are majorized by
the unrestricted sums appearing in `NumberField.Chebotarev.frobeniusDiscard_isLittleO` over
`L ^ <sigma>`.  In general there is no such identity for `ψ`: a prime power `𝔓 ^ m` with `m ≥ 2`
is selected by the `m`-th power of its Frobenius, and the prime of `K` below it need not have
class `C`.  So the transfer of `ψ` is only asymptotic,

```text
ψ_sigma^{L/E}(x) = (#G / (#C * orderOf sigma)) * ψ_C^{L/K}(x) + o(x),
```

obtained by removing the prime powers with `m ≥ 2` on both sides, applying the exact identity to
what remains, and discarding the relative primes of higher residue degree or above
`ramifiedPrimes K L`.

## Main results

* `NumberField.Chebotarev.primeTheta_fixedField_eq_mul_frobeniusTheta`: the residue-degree-one
  part of the relative Frobenius `ϑ` over `L ^ <sigma>`, away from the primes above
  `ramifiedPrimes K L`, is the fixed-field multiplicity times `frobeniusTheta K L C`.
* `NumberField.Chebotarev.frobeniusPsi_fixedField_sub_mul_frobeniusPsi_isLittleO`: the relative
  Frobenius `ψ` of `sigma` over `L ^ <sigma>` is the fixed-field multiplicity times
  `frobeniusPsi K L C`, up to `o(x)`.
* `NumberField.Chebotarev.frobeniusPsi_fixedField_asymptotic_iff`: hence the relative Frobenius
  `ψ` of `sigma` is `δ x + o(x)` exactly when `frobeniusPsi K L C` is `δ x + o(x)` divided by
  the fixed-field multiplicity.
* `NumberField.Chebotarev.frobeniusPsi_asymptotic_of_fixedField`: its specialisation at the cyclic
  value `δ = 1 / orderOf sigma`, which lands the Chebotarev value `#C / #G` over `K`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* S. Lang, *Algebraic Number Theory*, Chapter I, §5.
-/

 section

open _root_.Filter _root_.IntermediateField
open scoped _root_.Asymptotics _root_.NumberField
open _root_.IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev
end NumberField.Chebotarev
section NumberField.Chebotarev
open NumberField NumberField.Chebotarev

open _root_.TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]









/-- **Linear asymptotics of Frobenius `ψ` across the cyclic fixed field.** Let `sigma` represent
`C` and put `E = L ^ <sigma>`.  The relative Frobenius `ψ` of `sigma.toFixedFieldAlgEquiv` over `E`
is `δ x + o(x)` exactly when `frobeniusPsi K L C` is `(δ / (#G / (#C * orderOf sigma))) x + o(x)`.

This is the weighted counterpart of `hasDirichletDensity_frobeniusPrimeSet_fixedField_iff`.  It
carries an asymptotic for the fibre of `sigma` in the **cyclic** extension `L / E` down to the
class `C` over `K`, and conversely. -/
theorem solution (C : _root_.ConjClasses (L ≃ₐ[K] L))
    (sigma : L ≃ₐ[K] L) (hsigma : sigma ∈ C.carrier) {δ : ℝ} :
    (fun x : ℝ ↦ _root_.NumberField.Chebotarev.frobeniusPsi ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
        (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) x - δ * x) =o[_root_.Filter.atTop] (fun x : ℝ ↦ x) ↔
      (fun x : ℝ ↦ _root_.NumberField.Chebotarev.frobeniusPsi K L C x -
        δ / ((_root_.Nat.card (L ≃ₐ[K] L) / (_root_.Nat.card C.carrier * _root_.orderOf sigma) : ℕ) : ℝ) * x)
          =o[_root_.Filter.atTop] (fun x : ℝ ↦ x) := by
  set d : ℝ := ((_root_.Nat.card (L ≃ₐ[K] L) / (_root_.Nat.card C.carrier * _root_.orderOf sigma) : ℕ) : ℝ)
  have hd : d ≠ 0 := Nat.cast_ne_zero.mpr (C.card_div_card_carrier_mul_orderOf_pos sigma hsigma).ne'
  have h := _root_.NumberField.Chebotarev.frobeniusPsi_fixedField_sub_mul_frobeniusPsi_isLittleO C sigma hsigma
  -- The error over `E` is the `o(x)` contraction error plus `d` times the error over `K`.
  have key (x : ℝ) : _root_.NumberField.Chebotarev.frobeniusPsi ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
      (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) x - δ * x =
        (_root_.NumberField.Chebotarev.frobeniusPsi ↥(_root_.IntermediateField.fixedField (_root_.Subgroup.zpowers sigma)) L
          (_root_.ConjClasses.mk sigma.toFixedFieldAlgEquiv) x - d * _root_.NumberField.Chebotarev.frobeniusPsi K L C x) +
        d * (_root_.NumberField.Chebotarev.frobeniusPsi K L C x - δ / d * x) := by
    field_simp
    ring
  simp_rw [key]
  rw [h.add_iff_right, _root_.Asymptotics.isLittleO_const_mul_left_iff hd]



end NumberField.Chebotarev

end
end
