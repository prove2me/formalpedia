-- Prove2me | solution 1 for NumberField.exists_isTotallyPositive_sub_mem
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:16:49.498042+00:00
-- url     : https://prove2.me/submissions/e6e1179b-bbd8-43a5-9b8d-a5b90c6253ad

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Definitions.Def_TauCeti_NumberTheory_NumberField_TotallyPositive
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Algebra.Order.Ring.Units
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.Subgroup.Center
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.Tactic.Group

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Totally positive elements of a number field

An element `x` of a number field `K` is **totally positive** when it is strictly positive under
every real embedding `K →+* ℝ` — equivalently, at every real infinite place. This is the archimedean
positivity condition underlying the *narrow* class group of the multiquadratic roadmap (Layer 3):
the narrow class group `Cl⁺(K)` is the quotient of the fractional ideals by the principal ideals
admitting a totally positive generator. It surjects onto the ordinary class group `Cl(K)`
(forgetting the positivity condition), and the `2`-rank of `Cl⁺(K)` is what the genus-theory
`t - 1` formula (with `t` the number of ramified primes) computes for a **real quadratic** field
in the multiquadratic roadmap.

This file introduces the predicate and its multiplicative structure. The totally positive elements
are closed under multiplication and inversion and contain every nonzero square, so the totally
positive units form a subgroup of `Kˣ`. That subgroup is the kernel of the sign (signature) map on
units; the signs *not* realized by units measure the difference between `Cl⁺(K)` and `Cl(K)`.

The file also records that `totallyPositiveUnits` has **finite index** — a finite intersection, over
the real places, of the finite-index preimages of the positive units of `ℝ` — which is what makes
the narrow class group finite (see `NarrowClassGroup.Finite`).

## Main definitions and results

* `NumberField.IsTotallyPositive`: strict positivity at every real place, with
  `isTotallyPositive_iff` its introduction/elimination form.
* `NumberField.isTotallyPositive_one`, `IsTotallyPositive.mul`, `IsTotallyPositive.inv`,
  `isTotallyPositive_sq`: the multiplicative structure, including that nonzero squares are totally
  positive.
* `NumberField.isTotallyPositive_ratCast`: a positive rational number is totally positive, with
  `NumberField.isTotallyPositive_intCast` its integer special case.
* `NumberField.totallyPositiveUnits`: the subgroup of totally positive units of `Kˣ` (the
  kernel of the unit signature map), with `sq_mem_totallyPositiveUnits`. For a totally complex field
  it is everything (`totallyPositiveUnits_eq_top`), since total positivity is then vacuous
  (`not_isReal_of_isTotallyComplex` makes `IsTotallyPositive` `simp` to `True`).
* `NumberField.totallyPositiveIntegerUnits`: the corresponding subgroup of the arithmetic
  units `(𝓞 K)ˣ`, the preimage of `totallyPositiveUnits` under `(𝓞 K)ˣ → Kˣ`, with
  `mem_totallyPositiveIntegerUnits` and `sq_mem_totallyPositiveIntegerUnits`.
* `NumberField.exists_isTotallyPositive_sub_mem`: every residue class modulo a nonzero ideal of
  `𝓞 K` contains a nonzero totally positive integer.
* `NumberField.norm_nonneg_of_isTotallyPositive`: the field norm of a totally positive element is
  nonnegative, and `NumberField.norm_pos_of_isTotallyPositive`: for a nonzero such element it is
  strictly positive.
* `NumberField.finiteIndex_totallyPositiveUnits`: `totallyPositiveUnits` has finite index
  (via `Units.instFiniteIndexPosSubgroup` and the general `Subgroup.instFiniteIndexComap`).
-/

 section

open NumberField InfinitePlace

namespace NumberField
end NumberField
section NumberField
open NumberField

variable {K : Type*} [Field K]











/-- Every nonzero square is totally positive: at each real place its value is the square of a
nonzero real. -/
theorem NumberField.isTotallyPositive_sq {x : K} (hx : x ≠ 0) : _root_.NumberField.IsTotallyPositive (x ^ 2) :=
  isTotallyPositive_iff.mpr fun w hw => by
    rw [_root_.map_pow]; exact sq_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)















variable [NumberField K]









/-- **Every residue class modulo a nonzero ideal contains a nonzero totally positive integer.**
Adding a large enough multiple of the square of a nonzero element of `H` makes every real embedding
of `a` positive without moving `a` out of its class modulo `H`.

This is the archimedean adjustment behind any construction that has to reconcile an ideal-theoretic
congruence with the real places, such as choosing a coprime representative of a narrow ideal class
or a generator congruent to one modulo a ray-class modulus. -/
theorem solution {H : _root_.Ideal (𝓞 K)} (hH : H ≠ ⊥) (a : 𝓞 K) :
    ∃ b : 𝓞 K, b ≠ 0 ∧ b - a ∈ H ∧ _root_.NumberField.IsTotallyPositive (b : K) := by
  classical
  obtain ⟨q, hqH, hq0⟩ := _root_.Submodule.exists_mem_ne_zero_of_ne_bot hH
  -- The square of a nonzero element of `H` lies in `H` and is totally positive.
  have hpH : q ^ 2 ∈ H := by rw [_root_.sq]; exact _root_.Ideal.mul_mem_left H q hqH
  have hppos : _root_.NumberField.IsTotallyPositive ((q ^ 2 : 𝓞 K) : K) := by
    simpa only [_root_.map_pow] using
      _root_.NumberField.isTotallyPositive_sq (K := K) (RingOfIntegers.coe_ne_zero_iff.mpr hq0)
  set B : ℝ := ∑ w : {w : _root_.NumberField.InfinitePlace K // w.IsReal},
    |embedding_of_isReal w.2 (a : K)| / _root_.NumberField.InfinitePlace.embedding_of_isReal w.2 ((q ^ 2 : 𝓞 K) : K) with hB
  -- Any natural number exceeding `B` clears the negative values of `a` at every real place.
  have key : ∀ m : ℕ, B < m → _root_.NumberField.IsTotallyPositive ((a + (m : 𝓞 K) * q ^ 2 : 𝓞 K) : K) := by
    intro m hm w hw
    have hpw : 0 < _root_.NumberField.InfinitePlace.embedding_of_isReal hw ((q ^ 2 : 𝓞 K) : K) := hppos w hw
    have hle : |embedding_of_isReal hw (a : K)| /
        _root_.NumberField.InfinitePlace.embedding_of_isReal hw ((q ^ 2 : 𝓞 K) : K) ≤ B := by
      rw [hB]
      exact _root_.Finset.single_le_sum (f := fun v : {w : _root_.NumberField.InfinitePlace K // w.IsReal} =>
          |embedding_of_isReal v.2 (a : K)| / _root_.NumberField.InfinitePlace.embedding_of_isReal v.2 ((q ^ 2 : 𝓞 K) : K))
        (fun v _ => _root_.div_nonneg (_root_.abs_nonneg _) (hppos v.1 v.2).le)
        (a := (⟨w, hw⟩ : {w : _root_.NumberField.InfinitePlace K // w.IsReal})) (_root_.Finset.mem_univ _)
    have hlt : |embedding_of_isReal hw (a : K)| <
        m * _root_.NumberField.InfinitePlace.embedding_of_isReal hw ((q ^ 2 : 𝓞 K) : K) :=
      (_root_.div_lt_iff₀ hpw).mp (hle.trans_lt hm)
    have hval : _root_.NumberField.InfinitePlace.embedding_of_isReal hw ((a + (m : 𝓞 K) * q ^ 2 : 𝓞 K) : K) =
        _root_.NumberField.InfinitePlace.embedding_of_isReal hw (a : K) + m * _root_.NumberField.InfinitePlace.embedding_of_isReal hw ((q ^ 2 : 𝓞 K) : K) := by
      push_cast
      simp
    rw [hval]
    have := _root_.neg_abs_le (_root_.NumberField.InfinitePlace.embedding_of_isReal hw (a : K))
    linarith
  obtain ⟨n, hn⟩ := _root_.exists_nat_gt B
  -- One of two consecutive shifts is nonzero, and both are large enough.
  set m : ℕ := if a + (n : 𝓞 K) * q ^ 2 = 0 then n + 1 else n with hm
  have hmB : B < m := by
    rw [hm]
    split_ifs with h
    · exact hn.trans (by push_cast; linarith)
    · exact hn
  refine ⟨a + (m : 𝓞 K) * q ^ 2, ?_, by simpa using H.mul_mem_left _ hpH, key m hmB⟩
  rw [hm]
  split_ifs with h
  · have hshift : a + ((n + 1 : ℕ) : 𝓞 K) * q ^ 2 =
        (a + (n : 𝓞 K) * q ^ 2) + q ^ 2 := by
      push_cast
      ring
    rw [hshift, h, _root_.zero_add]
    exact _root_.pow_ne_zero 2 hq0
  · exact h









end NumberField

end
end
