-- Prove2me | solution 1 for MIPRE.CL.chunk_flatten_ofFn
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:29:54.379495+00:00
-- url     : https://prove2.me/submissions/56bfd072-0969-4d42-aa33-0cc2fd4da2e8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Bits.lean (solution of MIPRE.CL.chunk_flatten_ofFn);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL
open Cost.Data (chunk)
variable {k s : ℕ}
theorem _root_.solution {α : Type*} : ∀ {k : ℕ} (g : Fin k → List α),
    (∀ i, (g i).length = s) → ∀ i : Fin k, chunk s i (List.ofFn g).flatten = g i
  | 0, _, _, i => i.elim0
  | k + 1, g, hg, i => by
    rw [List.ofFn_succ, List.flatten_cons]
    refine Fin.cases ?_ (fun i' => ?_) i
    · simp only [chunk, Fin.val_zero, zero_mul, List.drop_zero]
      rw [List.take_append_of_le_length (hg 0).ge, List.take_of_length_le (hg 0).le]
    · have ih := solution (fun i => g i.succ) (fun i => hg i.succ) i'
      simp only [chunk, Fin.val_succ] at ih ⊢
      rw [List.drop_append, List.drop_of_length_le (by rw [hg 0]; nlinarith),
        List.nil_append, hg 0, show (i' + 1) * s - s = i' * s by rw [Nat.add_mul, one_mul]; omega]
      exact ih
end MIPRE.CL
