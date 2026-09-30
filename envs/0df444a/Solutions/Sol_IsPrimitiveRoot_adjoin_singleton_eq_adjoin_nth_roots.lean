-- Prove2me | solution 1 for IsPrimitiveRoot.adjoin_singleton_eq_adjoin_nth_roots
-- status  : ACCEPTED   (prove)
-- author  : @riccardo.brasca
-- created : 2026-09-29T21:15:49.308127+00:00
-- url     : https://prove2.me/submissions/9f35a338-d6c7-4220-a3c9-85823b30aabf

/- Transplanted from https://github.com/TauCetiProject/TauCeti at 948fe4751b1fe528b6d580c522ca5d743d47f185.
Original source copyright/license notices are retained below.
Generated exclusively from compiler declaration, command, and reference facts. -/
import Mathlib.NumberTheory.Cyclotomic.Basic

section
set_option autoImplicit true
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-!
# Adjoining roots of unity as an intermediate field

Adjoining one primitive `m`-th root of unity to `K` inside `M` gives the same intermediate field as
adjoining all the `m`-th roots of unity.

Mathlib proves the corresponding equalities for `Algebra.adjoin`, in
`IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic` and
`IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots`. This file carries them across
`IntermediateField.adjoin_toSubalgebra` to the `IntermediateField` lattice, which is where the
Galois correspondence needs them.

## Main results

* `IsPrimitiveRoot.adjoin_singleton_eq_adjoin_nth_roots`: `K(ζ) = K(μ_m)`.
-/

 section

open IntermediateField

/-- **Adjoining one primitive `m`-th root adjoins them all.** `K(ζ) = K(μ_m)` inside any
extension of `K` containing a primitive `m`-th root of unity `ζ`.

No algebraicity of the ambient extension is needed: each `m`-th root of unity is algebraic on
its own, being a root of the nonzero polynomial `X ^ m - 1`. -/
theorem solution {K M : Type*} [_root_.Field K] [_root_.Field M]
    [_root_.Algebra K M] {m : ℕ} [_root_.NeZero m] {ζ : M}
    (hζ : _root_.IsPrimitiveRoot ζ m) : _root_.IntermediateField.adjoin K {ζ} = _root_.IntermediateField.adjoin K {b : M | b ^ m = 1} := by
  -- an `m`-th root of unity is algebraic, being a root of unity
  have halg : ∀ b : M, b ^ m = 1 → _root_.IsAlgebraic K b := fun b hb ↦
    _root_.IsAlgebraic.of_pow (_root_.NeZero.pos m) (by rw [hb]; exact _root_.isAlgebraic_one)
  refine _root_.IntermediateField.toSubalgebra_injective ?_
  rw [_root_.IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (S := {ζ})
      (fun x hx ↦ halg x (by rw [Set.mem_singleton_iff.mp hx]; exact hζ.pow_eq_one)),
    _root_.IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (S := {b : M | b ^ m = 1}) (fun x hx ↦ halg x hx)]
  refine (_root_.IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_root_cyclotomic
    (A := K) hζ).symm.trans ?_
  refine (_root_.IsCyclotomicExtension.adjoin_roots_cyclotomic_eq_adjoin_nth_roots (A := K) hζ).trans ?_
  congr 1
  ext b
  simp [_root_.NeZero.ne m]

end
end
