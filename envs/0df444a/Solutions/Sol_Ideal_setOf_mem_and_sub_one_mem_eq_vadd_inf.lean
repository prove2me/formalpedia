-- Prove2me | solution 1 for Ideal.setOf_mem_and_sub_one_mem_eq_vadd_inf
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:39.467756+00:00
-- url     : https://prove2.me/submissions/04ef31d4-988e-4ec4-9865-af95a0ada891

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.RingTheory.Ideal.Operations

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# The elements of one ideal congruent to one modulo another

For ideals `I` and `J` of a commutative ring, the elements of `I` congruent to `1` modulo `J` form
a coset of `I ⊓ J` inside `I`, translated by any one of them.  Such an element exists exactly when
`I` and `J` are coprime, and coprimality also turns `I ⊓ J` into `I * J`.

This is the shape a counting argument wants: the set is a translate of a fixed subgroup, so it can
be enumerated by translating that subgroup once.

## Main results

* `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem`: the set is nonempty exactly when `I`
  and `J` are coprime;
* `Ideal.setOf_mem_and_sub_one_mem_eq_vadd_inf`: the set is a coset of `I ⊓ J`;
* `Ideal.setOf_mem_and_sub_one_mem_eq_vadd_mul`: the same coset written over `I * J`.
-/

 section

namespace Ideal
end Ideal
section Ideal
open Ideal

section Ring

variable {R : Type*} [Ring R] {I J : Ideal R}

open Pointwise in
/-- **The set is a coset of `I ⊓ J`.**  The elements of `I` congruent to `1` modulo `J` are a
translate of `I ⊓ J` by any one of them.  Only the additive structure of the ideals is used. -/
theorem solution {ξ : R} (hξI : ξ ∈ I) (hξJ : ξ - 1 ∈ J) :
    {x : R | x ∈ I ∧ x - 1 ∈ J} = ξ +ᵥ ((I ⊓ J : _root_.Ideal R) : _root_.Set R) := by
  ext x
  constructor
  · rintro ⟨hxI, hxJ⟩
    -- the difference of two elements is in `I` because both are, and in `J` because both are `1`
    refine ⟨x - ξ, ⟨I.sub_mem hxI hξI, ?_⟩, _root_.add_sub_cancel ξ x⟩
    simpa using J.sub_mem hxJ hξJ
  · rintro ⟨d, ⟨hdI, hdJ⟩, rfl⟩
    refine ⟨I.add_mem hξI hdI, ?_⟩
    -- `ξ +ᵥ d` is `ξ + d` by definition of the additive action of a ring on itself; no
    -- simp lemma states this, because `vadd_eq_add` is about the unbundled `+ᵥ` and the goal
    -- here is the beta-unreduced application left by `rintro`.
    change ξ + d - 1 ∈ J
    have : ξ + d - 1 = ξ - 1 + d := by abel
    rw [this]
    exact J.add_mem hξJ hdJ

end Ring

section CommRing

variable {R : Type*} [CommRing R] {I J : Ideal R}





end CommRing

end Ideal

end
end
