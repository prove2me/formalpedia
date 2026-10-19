-- Prove2me | solution 1 for MIPRE.LowDegree.coeff_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:50.192201+00:00
-- url     : https://prove2.me/submissions/e3ab2bf1-c154-49e4-a61b-cdba4cbafec6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SelfDualize.lean (solution of MIPRE.LowDegree.coeff_mul_self);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Theorems.Thm_MIPRE_LowDegree_add_self_injective

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LowDegree
section
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq G]
/-- In characteristic two, squaring is additive. -/
theorem add_mul_self_char_two {R : Type*} [CommRing R] (h2 : (2 : R) = 0) (x y : R) :
    (x + y) * (x + y) = x * x + y * y := by
  have e : (x + y) * (x + y) = x * x + y * y + 2 * (x * y) := by ring
  rw [e, h2, zero_mul, add_zero]
end
end MIPRE.LowDegree

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq G]
omit [Fintype F] in
theorem _root_.solution (hF : CharP F 2) (hG : Odd (Fintype.card G))
    (z : AddMonoidAlgebra F G) (g : G) :
    (z * z).coeff (g + g) = z.coeff g * z.coeff g := by
  have h2 : (2 : F) = 0 := by
    have := hF
    have := CharP.cast_eq_zero F 2
    rwa [show ((2 : ℕ) : F) = (2 : F) from by norm_num] at this
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [add_mul_self_char_two (two_eq_zero (G := G) hF), AddMonoidAlgebra.coeff_add,
        Finsupp.add_apply, hx, hy, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      have : ∀ a b : F, (a + b) * (a + b) = a * a + b * b :=
        add_mul_self_char_two h2
      rw [this]
  | single m r =>
      rw [AddMonoidAlgebra.single_mul_single, AddMonoidAlgebra.coeff_single,
        AddMonoidAlgebra.coeff_single, Finsupp.single_apply, Finsupp.single_apply]
      by_cases h : m = g
      · simp [h]
      · rw [if_neg h, if_neg (fun he => h (add_self_injective hG he)), mul_zero]
end MIPRE.LowDegree
