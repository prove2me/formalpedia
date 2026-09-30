-- Prove2me | solution 1 for NumberField.exists_auxiliaryPrime
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:38:22.418234+00:00
-- url     : https://prove2.me/submissions/5e1bcbef-34da-4a6e-b74a-2c08b1deee3c

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_RamifiedPrimes
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.LinearDisjoint
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.NumberTheory.NumberField.Discriminant.Different
import Mathlib.NumberTheory.NumberField.ExistsRamified
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.NumberTheory.PrimesCongruentOne
import Mathlib.NumberTheory.RamificationInertia.Unramified
import Mathlib.RingTheory.Polynomial.Eisenstein.IsIntegral
import Mathlib.RingTheory.RamificationInertia.Basic
import Theorems.Thm_TauCeti_RamificationInertia_ramificationIdx_mul_inertiaDeg_le_finrank

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Ramification indices in finite flat towers

This file records consequences of the fundamental identity for ramification and inertia in a finite
flat extension of domains. The number of primes above a prime and each prime's contribution are at
most the rank of the extension. Ramification also cancels in a tower when the absolute ramification
index at the top equals the absolute ramification index at the intermediate prime: multiplicativity
then forces the relative ramification index to be one.

The cancellation result is the local step used in the finite-place half of the genus-field
construction. At a rational prime dividing a prime discriminant, both the quadratic base and the
prime-discriminant compositum have absolute ramification index two; cancellation then shows that
the compositum is unramified over the quadratic base.

## Main results

* `TauCeti.RamificationInertia.ncard_primesOver_le_finrank`: the number of primes above a prime is
  at most the rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_mul_inertiaDeg_le_finrank`: the contribution of one
  prime to the fundamental identity is at most the rank of the extension.
* `TauCeti.RamificationInertia.ramificationIdx_le_finrank`: a ramification index is at most the
  rank of a finite flat extension.
* `TauCeti.RamificationInertia.ramificationIdx_eq_one_of_eq_ramificationIdx`: equal absolute
  ramification indices at two levels of a tower force relative ramification index one.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_eq_ramificationIdx`: if that equality
  holds at every prime above an intermediate prime, then the intermediate prime is unramified in
  the top ring.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_forall_ramificationIdx_le`: it suffices to bound
  every absolute ramification index upstairs by the intermediate absolute ramification index.
* `TauCeti.RamificationInertia.isUnramifiedIn_of_finrank_le_of_under_ramificationIdx_eq_one`: a
  transverse unramified subextension of sufficiently small relative degree supplies that bound.
* `TauCeti.RamificationInertia.isUnramifiedAt_of_isUnramifiedIn`: unramifiedness over the
  base descends from an integral extension to the subring below it, for `S` integral and
  torsion-free over the Dedekind domain `R`, with `R` and `S` both essentially of finite type over
  the base `A` and `A ≤ R ≤ S` a scalar tower. The base ring and the ideal are arbitrary.
-/

 section

open Ideal Module

namespace TauCeti.RamificationInertia

section Bounds

variable {R S : Type*} [CommRing R] [IsDomain R] [CommRing S] [Algebra R S]
  [Module.Finite R S] [Module.Flat R S]





/-- **A ramification index is at most the rank of a finite flat extension.** For a prime `q` of
`S` above a prime `p` of `R`, `e(q / p) ≤ Module.finrank R S`. -/
theorem ramificationIdx_le_finrank (p : Ideal R) [p.IsPrime] (q : Ideal S)
    [q.IsPrime] [q.LiesOver p] : q.ramificationIdx R ≤ finrank R S :=
  le_trans (Nat.le_mul_of_pos_right _ (Ideal.inertiaDeg_pos q R))
    (ramificationIdx_mul_inertiaDeg_le_finrank p q)

end Bounds

section Tower

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T] [Algebra R S] [Algebra R T]
  [Algebra S T] [IsScalarTower R S T] [Module.Finite R S] [Module.Flat S T]









end Tower

section Descent

variable {A R S : Type*} [CommRing A] [CommRing R] [IsDedekindDomain R] [CommRing S] [IsDomain S]
  [Algebra A R] [Algebra A S] [Algebra R S] [IsScalarTower A R S] [Algebra.IsIntegral R S]
  [Module.IsTorsionFree R S] [Algebra.EssFiniteType A R] [Algebra.EssFiniteType A S]

-- Source. Recovered from the retired PR #5538, at commit
-- 70421db267d9bd6252256f873d27e99e739a931c.



end Descent

end TauCeti.RamificationInertia

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
# Irreducibility of the cyclotomic polynomial from the degree of a cyclotomic extension

Mathlib proves `[L : K] = φ n` for an `n`-th cyclotomic extension `L / K` once `Φ_n` is known to be
irreducible over `K` (`IsCyclotomicExtension.finrank`). This file records the converse: the degree
of `L / K` is always at most `φ n`, and as soon as it is at least `φ n` the polynomial `Φ_n` is
irreducible over `K`. That converse and Mathlib's forward direction give the equivalence
`IsCyclotomicExtension.irreducible_cyclotomic_iff_finrank_eq_totient`.

## Main results

* `IsCyclotomicExtension.finrank_le_totient`: `[L : K] ≤ φ n`.
* `IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank`: if `φ n ≤ [L : K]` then
  `Φ_n` is irreducible over `K`.
* `IsCyclotomicExtension.irreducible_cyclotomic_iff_finrank_eq_totient`: `Φ_n` is irreducible over
  `K` if and only if `[L : K] = φ n`.
* `irreducible_cyclotomic_of_coprime_finrank`: irreducibility is preserved by a finite base change
  whose degree is coprime to `φ n`.
* `irreducible_cyclotomic_two_pow_ratPadic`: every `2`-power cyclotomic polynomial is irreducible
  over `ℚ₂`.

## References

This is the degree bookkeeping of Milne, *Algebraic Number Theory*, proof of Proposition 6.2, and
of Sharifi, *Algebraic Number Theory*, proof of Lemma 3.1.13, where the base field is `ℚ`.
-/

 section

open Polynomial

namespace IsCyclotomicExtension

variable {n : ℕ} [NeZero n] (K : Type*) [Field K] (L : Type*) [CommRing L] [IsDomain L]
  [Algebra K L] [IsCyclotomicExtension {n} K L]

private theorem finrank_eq_natDegree_minpoly_zeta :
    Module.finrank K L = (minpoly K (zeta n K L)).natDegree := by
  -- `L = K(ζ)` has the power basis `1, ζ, …` of length `deg (minpoly K ζ)`.
  -- Source: Mathlib, proof of `IsCyclotomicExtension.finrank`.
  rw [((zeta_spec n K L).powerBasis K).finrank, IsPrimitiveRoot.powerBasis_dim]

private theorem minpoly_zeta_dvd_cyclotomic : minpoly K (zeta n K L) ∣ cyclotomic n K :=
  -- A primitive `n`-th root of unity is a root of `Φ_n`.
  -- Mathlib's `IsPrimitiveRoot.minpoly_dvd_cyclotomic` does not apply here: it is stated over
  -- `ℤ`, needs the root to lie in `K` itself, and assumes `[CharZero K]`.
  have : NeZero (n : L) := IsCyclotomicExtension.neZero n K L
  minpoly.dvd K _ (aeval_zeta n K L)



/-- **A cyclotomic extension of full degree has irreducible cyclotomic polynomial.** This is the
converse of Mathlib's `IsCyclotomicExtension.finrank`, and with it gives the equivalence
`irreducible_cyclotomic_iff_finrank_eq_totient`.

Source: Milne, *Algebraic Number Theory*, proof of Prop. 6.2 ("(3.34) implies
`[ℚ[ζ] : ℚ] ≥ φ(p^r)`. This proves (a)"); Sharifi, proof of Lemma 3.1.13 ("which forces
`[ℚ(µ_{p^r}) : ℚ] = p^{r−1}(p − 1)`"). -/
theorem irreducible_cyclotomic_of_totient_le_finrank (h : n.totient ≤ Module.finrank K L) :
    Irreducible (cyclotomic n K) := by
  have hint : IsIntegral K (zeta n K L) := (integral {n} K L).isIntegral _
  have hdeg : (cyclotomic n K).natDegree ≤ (minpoly K (zeta n K L)).natDegree := by
    rwa [natDegree_cyclotomic, ← finrank_eq_natDegree_minpoly_zeta K L]
  rw [eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) (cyclotomic.monic n K)
    (minpoly_zeta_dvd_cyclotomic K L) hdeg]
  exact minpoly.irreducible hint



end IsCyclotomicExtension

namespace TauCeti



section BaseChange

variable {n : ℕ} {F : Type*} [Field F]
  {K : Type*} [Field K] [Algebra F K] [FiniteDimensional F K]



end BaseChange

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
# Ramification indices in an extension of number fields

A consequence of the general ramification bounds for the rings of integers of number fields.
`TauCeti.NumberTheory.RamificationInertia.Tower` states it for a finite flat extension of
domains; here it is transported to the fields themselves, so the bound is `[F : K]` rather than
the rank of `𝓞 F` over `𝓞 K`.

## Main results

* `Ideal.ramificationIdx_le_finrank_of_numberField`: for a prime `𝔔` of `𝓞 F` in an extension
  `F / K` of number fields, `e(𝔔 / 𝓞 K) ≤ [F : K]`.
* `Ideal.finrank_eq_one_of_ramificationIdx_eq_finrank`: in a tower `K ≤ E ≤ B`, a
  prime of `𝓞 B` with `e(𝔔 / 𝓞 E) = [B : K]` — the full tower degree, not merely `[B : E]` —
  forces `[E : K] = 1`.
-/

 section

open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

-- Source. Both declarations are recovered from the retired PR #5538, at commit
-- 70421db267d9bd6252256f873d27e99e739a931c. They are specified by the Chebotarev roadmap:
-- `TauCetiRoadmap/Chebotarev/README.md` §7.2 step 1 asks that `ℚ(ζ_q)/ℚ`, being totally ramified
-- at `q`, have "every subfield of `ℚ(ζ_q)` other than `ℚ` ramified at `q`" — which is
-- `Ideal.finrank_eq_one_of_ramificationIdx_eq_finrank` with `E` that subfield, and the bound
-- `Ideal.ramificationIdx_le_finrank_of_numberField` is what makes the ramification index reach the
-- degree there.

/-- **A relative ramification index is at most the degree of the extension.** For a prime `𝔔` of
`𝓞 F` in an extension `F / K` of number fields, `e(𝔔 / 𝓞 K) ≤ [F : K]`.

It is the number-field form of `TauCeti.RamificationInertia.ramificationIdx_le_finrank`, whose
bound is the rank of `𝓞 F` over `𝓞 K`; the two agree, and this is the one a caller holding a field
extension can use directly. -/
theorem _root_.Ideal.ramificationIdx_le_finrank_of_numberField {F : Type*} [Field F]
    [NumberField F] [Algebra K F] (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] :
    𝔔.ramificationIdx (𝓞 K) ≤ Module.finrank K F :=
  -- The fundamental identity `∑ eᵢ fᵢ = [F : K]` bounds each `eᵢ`, and `[𝓞 F : 𝓞 K] = [F : K]`.
  (TauCeti.RamificationInertia.ramificationIdx_le_finrank (𝔔.under (𝓞 K)) 𝔔).trans_eq
    (IsFractionRing.finrank_eq (𝓞 K) K (𝓞 F) F).symm



end TauCeti.NumberField

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
# Unramifiedness makes the cyclotomic polynomial irreducible over a number field

Let `K` be a number field and `p` a prime that is unramified in `K`. Then the cyclotomic polynomial
`Φ_{p^(k+1)}` is irreducible over `K` for every `k`; in particular `Φ_p` is, so
`[K(ζ_p) : K] = p - 1`. For the Galois group itself, feed that irreducibility to Mathlib's
`IsCyclotomicExtension.autEquivPow`, which yields `Gal(K(ζ_p)/K) ≃* (ZMod p)ˣ`; this file proves
irreducibility and the ramification behind it, and does not restate that consequence.

The mechanism is ramification, not an intersection of fields. Let `F / K` be a `p^(k+1)`-th
cyclotomic extension and `𝔔` a prime of `𝓞 F` above `p`. Inside `F` the subfield `ℚ(ζ)` is the
`p^(k+1)`-th cyclotomic field over `ℚ`, in which `p` is totally ramified with index
`φ(p^(k+1))`; ramification indices multiply in towers, so `e(𝔔 / p) ≥ φ(p^(k+1))`. On the other
hand `e(𝔔 / p) = e(𝔔 / 𝔮) · e(𝔮 / p)` with `𝔮 = 𝔔 ∩ 𝓞 K`, and `e(𝔮 / p) = 1` because `p` is
unramified in `K`. Hence `e(𝔔 / 𝔮) ≥ φ(p^(k+1))`, while `e(𝔔 / 𝔮) ≤ [F : K]`. So
`[F : K] ≥ φ(p^(k+1))`, which is irreducibility of `Φ_{p^(k+1)}` over `K` by
`IsCyclotomicExtension.irreducible_cyclotomic_of_totient_le_finrank`.

The intersection `L ⊓ K(ζ_p) = ⊥` for an extension `L / K` gives none of this: it constrains `L`,
whereas `[K(ζ_p) : K]` is a proper divisor of `p - 1` exactly when `K ∩ ℚ(ζ_p) ≠ ℚ`. The witness
`K = ℚ(√5)`, `p = 5` is `Polynomial.not_irreducible_cyclotomic_five_of_sq_eq_five`.

## Main results

* `IsPrimitiveRoot.totient_le_ramificationIdx`: a primitive `p^(k+1)`-th root of unity in a
  number field `F` forces `φ(p^(k+1)) ≤ e(𝔔 ∣ ℤ)` for every prime `𝔔` of `𝓞 F` above `p`.
* `IsCyclotomicExtension.totient_le_finrank_of_unramified`: `φ(p^(k+1)) ≤ [F : K]` when `p` is
  unramified in `K`.
* `IsCyclotomicExtension.ramificationIdx_eq_totient`: every prime of `𝓞 F` above `p` has
  ramification index exactly `φ(p^(k+1))` over `𝓞 K`, so `F / K` is totally ramified there.
* `IsCyclotomicExtension.inf_eq_bot_prime_pow_of_unramified`: for intermediate fields `A` and `B`
  of `Ω / K` with `B` a `p^(k+1)`-th cyclotomic extension, `p` unramified in `A` gives
  `A ⊓ B = ⊥`.
* `IsCyclotomicExtension.inf_eq_bot_of_unramified`: the prime case.
* `IsCyclotomicExtension.irreducible_cyclotomic_prime_pow_of_unramified`: `Φ_{p^(k+1)}` is
  irreducible over `K` when `p` is unramified in `K`.
* `IsCyclotomicExtension.irreducible_cyclotomic_of_unramified`: the prime case.

## References

Unramifiedness, rather than an intersection of fields, is what gives the full cyclotomic degree.

Total ramification of `ℚ(ζ_{p^r})` at `p` is Milne, *Algebraic Number Theory*, Proposition 6.2,
and Sharifi, *Algebraic Number Theory*, Lemma 3.1.13; the ramification bookkeeping is Sharifi,
Remark 2.5.7 and Theorem 2.5.11. The argument mirrors
`TauCeti.Multiquadratic.ramificationIdx_eq_two_of_liesOver_primeDiscriminantPrime`.

The tower and discriminant bookkeeping was mined from the private declarations
`prime_dvd_natAbs_discr_cyclotomic_dvd` and `cyclotomicField_finrank_eq` in
`CebotarevDensity/Abelian.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) at commit `8575c9df1ae0a61120ab5c964c7911414254bec7`. The source states those
through coprimality to the discriminant; the results here are restated through unramifiedness.
-/

 section

open Polynomial
open scoped NumberField


namespace IsCyclotomicExtension

variable {K : Type*} [Field K] [NumberField K]

/-- **A primitive `p^(k+1)`-th root of unity forces ramification at least `φ(p^(k+1))` above
`p`.** For any number field `F` containing such a root, every prime of `𝓞 F` above `p` has
ramification index at least `φ(p^(k+1))` over `ℤ`.

No cyclotomic-extension hypothesis is needed: the root alone pins `ℚ(ζ)` inside `F`, and `p` is
totally ramified there.

Source: Milne, *Algebraic Number Theory*, Proposition 6.2(c); Sharifi, Lemma 3.1.13. -/
theorem _root_.IsPrimitiveRoot.totient_le_ramificationIdx {p k : ℕ} [Fact p.Prime] {F : Type*}
    [Field F] [NumberField F] {ζ : F} (hζ : IsPrimitiveRoot ζ (p ^ (k + 1)))
    (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime]
    [𝔔.LiesOver (Ideal.span {(p : ℤ)})] : (p ^ (k + 1)).totient ≤ 𝔔.ramificationIdx ℤ := by
  -- `p` is totally ramified in `ℚ(ζ)`: Milne, Prop. 6.2(c) (`(p) = (π)^e` with `e = φ(p^r)`);
  -- Sharifi, Lemma 3.1.13 ("It is totally ramified").
  have : IsCyclotomicExtension {p ^ (k + 1)} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  -- Indices multiply in towers: Sharifi, Remark 2.5.7 ("`e_{P/p} = e_{P/𝔓} e_{𝔓/p}`").
  have h := (𝔔.under (𝓞 (IntermediateField.adjoin ℚ {ζ}))).ramificationIdx_below_le (R := ℤ) 𝔔
  rwa [Rat.ramificationIdx_eq_of_prime_pow p k, ← Nat.totient_prime_pow_succ Fact.out] at h

private theorem totient_le_ramificationIdx (p k : ℕ) [Fact p.Prime] {F : Type*} [Field F]
    [NumberField F] [Algebra K F] [IsCyclotomicExtension {p ^ (k + 1)} K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
    Algebra.IsUnramifiedAt ℤ 𝔮) (𝔔 : Ideal (𝓞 F)) [𝔔.IsPrime] [𝔔.LiesOver (Ideal.span {(p : ℤ)})] :
    (p ^ (k + 1)).totient ≤ 𝔔.ramificationIdx (𝓞 K) := by
  -- First tower `ℤ ⊆ 𝓞 ℚ(ζ) ⊆ 𝓞 F`, through a primitive root: `e(𝔔 / p) ≥ φ(p^(k+1))`.
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot (S := {p ^ (k + 1)}) K F
    (Set.mem_singleton _) (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)
  -- Second tower `ℤ ⊆ 𝓞 K ⊆ 𝓞 F`: indices multiply (Sharifi, Remark 2.5.7) and `e(𝔮 / p) = 1`
  -- because `p` is unramified in `K`, so `e(𝔔 / p) = e(𝔔 / 𝔮)`.
  simpa only [Ideal.ramificationIdx_tower (R := ℤ) (𝔔.under (𝓞 K)) 𝔔,
    Algebra.IsUnramifiedIn.ramificationIdx_eq_one (R := ℤ) hur
      (𝔓 := 𝔔.under (𝓞 K)) inferInstance, one_mul] using
    hζ.totient_le_ramificationIdx 𝔔

/-- **The degree of a cyclotomic extension above an unramified prime is at least `φ(p^(k+1))`.**
Unlike `IsPrimitiveRoot.lcm_totient_le_finrank` it assumes no irreducibility, so it can feed
`irreducible_cyclotomic_of_totient_le_finrank` rather than follow from it.

Source: Sharifi, Theorem 2.5.11 (`∑ eᵢ fᵢ = [L : K]`); Milne, Theorem 3.34. -/
theorem totient_le_finrank_of_unramified (p k : ℕ) [Fact p.Prime] (F : Type*) [Field F]
    [Algebra K F] [IsCyclotomicExtension {p ^ (k + 1)} K F]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) : (p ^ (k + 1)).totient ≤ Module.finrank K F := by
  have : FiniteDimensional K F := finiteDimensional {p ^ (k + 1)} K F
  have : NumberField F := .of_module_finite K F
  -- A prime of `𝓞 F` above `p`: Sharifi, Thm 2.5.11 (`pB = P₁^{e₁} ⋯ P_g^{e_g}` with `g ≥ 1`).
  obtain ⟨𝔔, _, _⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (Ideal.span {(p : ℤ)})
    (S := 𝓞 F)
  -- `𝔔` has relative ramification index at least `φ(p^(k+1))` over `𝓞 K`, and a ramification
  -- index never exceeds the degree of the extension.
  exact (totient_le_ramificationIdx p k hur 𝔔).trans 𝔔.ramificationIdx_le_finrank_of_numberField








variable (K) in
/-- **Unramifiedness gives irreducibility of `Φ_{p^(k+1)}`.** If the prime `p` is unramified in the
number field `K`, then the `p^(k+1)`-th cyclotomic polynomial is irreducible over `K`.

`hur` is definitionally Mathlib's `Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})`, so a proof
of that predicate can be passed directly; the bundled `Algebra.Unramified ℤ (𝓞 K)` is far stronger,
and forces `Module.finrank ℚ K = 1` by `NumberField.finrank_eq_one_of_unramified`, hence a
`ℚ`-algebra isomorphism `K ≃ₐ[ℚ] ℚ` rather than equality of types. Unramifiedness is sufficient but
not necessary: irreducibility holds exactly when `K ∩ ℚ(ζ_{p^(k+1)}) = ℚ`. For `k = 0` see
`irreducible_cyclotomic_of_unramified`.

Source: Milne, Prop. 6.2 and Sharifi, Lemma 3.1.13 for the base `ℚ`. -/
theorem irreducible_cyclotomic_prime_pow_of_unramified (p k : ℕ) [Fact p.Prime]
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(p : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) : Irreducible (cyclotomic (p ^ (k + 1)) K) :=
  -- `p` unramified in `K` forces the canonical `p^(k+1)`-th cyclotomic extension of `K` to have
  -- degree at least `φ(p^(k+1))`, the full degree of `Φ_{p^(k+1)}`.
  irreducible_cyclotomic_of_totient_le_finrank K (CyclotomicField (p ^ (k + 1)) K) <|
    totient_le_finrank_of_unramified p k _ hur

variable (K) in
/-- **Unramifiedness gives irreducibility of `Φ_q`.** If the prime `q` is unramified in the number
field `K`, then the `q`-th cyclotomic polynomial is irreducible over `K`, hence
`[K(ζ_q) : K] = q - 1`.

`hur` is definitionally Mathlib's `Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(q : ℤ)})`, so a proof
of that predicate can be passed directly. `L ⊓ K(ζ_q) = ⊥` is no substitute: it constrains `L`, not
`K ∩ ℚ(ζ_q)`, which is what irreducibility is equivalent to. See
`Polynomial.not_irreducible_cyclotomic_five_of_sq_eq_five` for the witness.

Source: the case `k = 0` of `irreducible_cyclotomic_prime_pow_of_unramified`. -/
theorem irreducible_cyclotomic_of_unramified (q : ℕ) (hq : q.Prime)
    (hur : ∀ (𝔮 : Ideal (𝓞 K)) [𝔮.IsPrime] [𝔮.LiesOver (Ideal.span {(q : ℤ)})],
      Algebra.IsUnramifiedAt ℤ 𝔮) : Irreducible (cyclotomic q K) := by
  -- The case `k = 0` of the prime-power result, where `q ^ (0 + 1)` reduces to `q`.
  have : Fact q.Prime := ⟨hq⟩
  simpa using irreducible_cyclotomic_prime_pow_of_unramified K q 0 hur

end IsCyclotomicExtension


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
# The ramified rational primes of a number field

The genus theory of a quadratic field is governed by the number `t` of rational primes that ramify
in it: the genus field has degree `2 ^ t` over `ℚ` and the `2`-rank of the narrow class group is
`t - 1`. This file names that set of primes and records its basic properties.

Mathlib phrases ramification of a rational prime `p` in a number field `K` as
`Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})`, and characterises it by divisibility of the
discriminant (`NumberField.not_dvd_discr_iff_isUnramifiedIn`). We package the negation as a set of
natural primes, which is the form in which `t` is counted.

## Main definitions

* `NumberField.ramifiedPrimes`: the set of natural primes ramifying in `K`.

## Main results

* `NumberField.mem_ramifiedPrimes_iff_dvd_discr`: a prime ramifies iff it divides the
  discriminant.
* `NumberField.coprime_natAbs_discr_of_isUnramifiedIn`: an unramified prime is coprime to the
  discriminant.
* `AlgEquiv.ramifiedPrimes_eq`: isomorphic number fields have the same ramified primes.
* `NumberField.ramifiedPrimes_rat`: no prime ramifies in `ℚ`.
* `NumberField.finite_ramifiedPrimes`: only finitely many primes ramify.
* `NumberField.ramifiedPrimes_nonempty`: some prime ramifies, unless `K = ℚ`
  (Minkowski, via `NumberField.exists_not_isUnramifiedIn`).
-/

 section

open scoped NumberField

namespace NumberField

variable (K : Type*) [Field K]



variable {K}

/-- The defining condition for membership in `ramifiedPrimes`. -/
@[simp]
theorem mem_ramifiedPrimes_iff {p : ℕ} :
    p ∈ ramifiedPrimes K ↔
      p.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) :=
  Iff.rfl



variable [NumberField K]

/-- **Ramification is divisibility of the discriminant.** A natural prime `p` ramifies in `K` iff
`p` divides `NumberField.discr K`. This is `NumberField.not_dvd_discr_iff_isUnramifiedIn` in the
`ramifiedPrimes` packaging. -/
theorem mem_ramifiedPrimes_iff_dvd_discr {p : ℕ} (hp : p.Prime) :
    p ∈ ramifiedPrimes K ↔ (p : ℤ) ∣ NumberField.discr K := by
  rw [mem_ramifiedPrimes_iff, and_iff_right hp,
    ← NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hp),
    not_not]





-- Source. The hypothesis this discharges is
-- `hcop : ((NumberField.discr L).natAbs).Coprime m` in the Birkbeck--Brasca Chebotarev
-- development, CBirkbeck/chebotarev-density (Apache-2.0), branch `development` at
-- `8575c9df1ae0a61120ab5c964c7911414254bec7`. There `CebotarevDensity/Abelian.lean` carries it
-- undischarged throughout, obtaining `p ∤ discr E` from
-- `NumberField.not_dvd_discr_iff_forall_liesOver` inline. The statement below is that hypothesis;
-- deriving it from `Algebra.IsUnramifiedIn` is not done in the source, which propagates it.



/-- **Only finitely many primes ramify**, since they all divide the nonzero integer
`NumberField.discr K`. -/
theorem finite_ramifiedPrimes : (ramifiedPrimes K).Finite := by
  have hne : (NumberField.discr K).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  refine Set.Finite.subset (NumberField.discr K).natAbs.divisors.finite_toSet fun p hp => ?_
  exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr
    ⟨Int.natCast_dvd.mp ((mem_ramifiedPrimes_iff_dvd_discr hp.1).mp hp), hne⟩)



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
# The auxiliary prime

The Chebotarev density argument repeatedly needs a rational prime that is simultaneously large,
congruent to `1` modulo a prescribed level, unramified in two number fields, and such that the
cyclotomic polynomial stays irreducible over the base. This file produces one, with all of those
conditions as conclusions rather than as obligations left to the caller.

## Main results

* `NumberField.exists_auxiliaryPrime`

## Implementation notes

The conditions are conclusions rather than obligations on the caller because they are needed
together: a caller holding only the congruence would have to re-derive the bound against the
ramified primes of both fields before it could discharge the rest.
-/

 section

open Polynomial
open scoped NumberField

namespace NumberField
end NumberField
section NumberField
open NumberField

/-- **The auxiliary prime.** Given number fields `K` and `L`, a level `n ≠ 0` and a bound `N`,
there is a rational prime `q` with `N < q`, congruent to `1` modulo `n`, unramified in both `K`
and `L`, and with `Φ_q` irreducible over `K`.

`n ∣ q - 1` is recorded alongside `q ≡ 1 [MOD n]` because the two are used in different forms
downstream and the translation needs `1 ≤ q`, which is not available to a caller holding only the
congruence. -/
theorem solution (K L : Type*) [_root_.Field K] [_root_.NumberField K] [_root_.Field L] [_root_.NumberField L]
    (n N : ℕ) (hn : n ≠ 0) :
    ∃ q : ℕ, q.Prime ∧ N < q ∧ q ≡ 1 [MOD n] ∧ n ∣ q - 1 ∧
      _root_.Algebra.IsUnramifiedIn (𝓞 K) (_root_.Ideal.span {(q : ℤ)}) ∧
      _root_.Algebra.IsUnramifiedIn (𝓞 L) (_root_.Ideal.span {(q : ℤ)}) ∧
      _root_.Irreducible (_root_.Polynomial.cyclotomic q K) := by
  -- Push the bound past every prime that ramifies in either field; both sets are finite.
  obtain ⟨SK, hSK⟩ := (_root_.NumberField.finite_ramifiedPrimes (K := K)).bddAbove
  obtain ⟨SL, hSL⟩ := (_root_.NumberField.finite_ramifiedPrimes (K := L)).bddAbove
  obtain ⟨q, hq, hqgt, hqmod⟩ := _root_.Nat.exists_prime_gt_modEq_one (k := n) (_root_.Max.max N (_root_.Max.max SK SL)) hn
  have hqN : N < q := _root_.lt_of_le_of_lt (_root_.le_max_left _ _) hqgt
  have hurK : _root_.Algebra.IsUnramifiedIn (𝓞 K) (_root_.Ideal.span {(q : ℤ)}) := by
    by_contra h
    have hle : q ≤ SK := hSK (mem_ramifiedPrimes_iff.mpr ⟨hq, h⟩)
    exact _root_.absurd hle (not_le.mpr
      (_root_.lt_of_le_of_lt (_root_.le_trans (_root_.le_max_left _ _) (_root_.le_max_right _ _)) hqgt))
  have hurL : _root_.Algebra.IsUnramifiedIn (𝓞 L) (_root_.Ideal.span {(q : ℤ)}) := by
    by_contra h
    have hle : q ≤ SL := hSL (mem_ramifiedPrimes_iff.mpr ⟨hq, h⟩)
    exact _root_.absurd hle (not_le.mpr
      (_root_.lt_of_le_of_lt (_root_.le_trans (_root_.le_max_right _ _) (_root_.le_max_right _ _)) hqgt))
  refine ⟨q, hq, hqN, hqmod, ?_, hurK, hurL,
    _root_.IsCyclotomicExtension.irreducible_cyclotomic_of_unramified K q hq hurK⟩
  exact (_root_.Nat.modEq_iff_dvd' hq.one_lt.le).mp hqmod.symm

end NumberField

end
end
