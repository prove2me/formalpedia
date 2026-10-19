-- Prove2me | solution 1 for MIPRE.LowDegree.exists_pow_succ_eq_self_of_square_bijective
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:46:08.44755+00:00
-- url     : https://prove2.me/submissions/2ba910f1-6ee4-45b8-a464-c4f8141f5000

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/FiniteReducedComponents.lean (solution of MIPRE.LowDegree.exists_pow_succ_eq_self_of_square_bijective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_LowDegree_FiniteReducedComponents

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
variable {R : Type*} [CommRing R] [Finite R]
theorem _root_.solution
    (hsq : Function.Bijective (fun x : R => x * x)) (x : R) :
    ∃ n : ℕ, 0 < n ∧ x ^ (n + 1) = x := by
  classical
  let e : Equiv.Perm R := Equiv.ofBijective (fun x : R => x * x) hsq
  have ho : 0 < orderOf e := orderOf_pos e
  have hp : ((fun x : R => x * x)^[orderOf e]) x = x := by
    have hf : (e : R → R) = (fun x : R => x * x) := rfl
    have h := congrArg (fun f : Equiv.Perm R => f x) (pow_orderOf_eq_one e)
    simpa only [Equiv.Perm.coe_pow, Equiv.Perm.coe_one, Function.id_def, hf] using h
  have he (n : ℕ) : ((fun x : R => x * x)^[n]) x = x ^ (2 ^ n) := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, ← pow_two, ← pow_mul, pow_succ]
  rw [he] at hp
  refine ⟨2 ^ orderOf e - 1, ?_, ?_⟩
  · have htwo : 2 ≤ 2 ^ orderOf e := by
      exact Nat.le_pow ho
    omega
  · rw [Nat.sub_add_cancel (Nat.one_le_pow _ _ (by decide))]
    exact hp
end MIPRE.LowDegree
