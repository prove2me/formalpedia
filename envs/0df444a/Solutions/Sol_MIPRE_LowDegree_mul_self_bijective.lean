-- Prove2me | solution 1 for MIPRE.LowDegree.mul_self_bijective
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:29:33.892857+00:00
-- url     : https://prove2.me/submissions/ca0c893c-a6d0-44ac-b83b-05654c50687b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/LowDegree/SelfDualize.lean (solution of MIPRE.LowDegree.mul_self_bijective);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.FieldTheory.Finite.Basic
import Definitions.Def_MIPRE_Foundations_LowDegree_SelfDualize
import Theorems.Thm_MIPRE_LowDegree_coeff_mul_self

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LowDegree
open Finset
variable {G : Type*} [AddCommGroup G] [Fintype G]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq G]
theorem _root_.solution (hF : CharP F 2) (hG : Odd (Fintype.card G)) :
    Function.Bijective fun x : AddMonoidAlgebra F G => x * x := by
  have : Finite (AddMonoidAlgebra F G) :=
    Finite.of_injective AddMonoidAlgebra.coeff AddMonoidAlgebra.coeff_injective
  refine Finite.injective_iff_bijective.mp fun x y hxy => ?_
  have hz : (x - y) * (x - y) = 0 := by
    have e : (x - y) * (x - y) = x * x - y * y - 2 * (x * y) + 2 * (y * y) := by ring
    rw [e, hxy, sub_self, two_eq_zero (G := G) hF, zero_mul, zero_mul, zero_sub, neg_zero,
      add_zero]
  refine sub_eq_zero.mp (AddMonoidAlgebra.coeff_injective (Finsupp.ext fun g => ?_))
  have := coeff_mul_self hF hG (x - y) g
  rw [hz] at this
  simpa using (mul_self_eq_zero.mp this.symm)
end MIPRE.LowDegree
