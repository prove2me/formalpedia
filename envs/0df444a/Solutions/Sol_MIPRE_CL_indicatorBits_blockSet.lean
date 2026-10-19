-- Prove2me | solution 1 for MIPRE.CL.indicatorBits_blockSet
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:29:38.204879+00:00
-- url     : https://prove2.me/submissions/cef70e57-3298-428c-9552-63d444cae303

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/Bits.lean (solution of MIPRE.CL.indicatorBits_blockSet);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Cost.Data (chunk)
variable {k s : ℕ}
theorem finProdFinEquiv_val (i : Fin k) (j : Fin s) :
    ((finProdFinEquiv (i, j) : Fin (k * s)) : ℕ) = j + s * i := rfl
end
end MIPRE.CL

namespace MIPRE.CL
section
open Cost.Data (chunk)
variable {k s : ℕ}
/-- A list indexed by `Fin (k s)` is the concatenation of its `k` blocks of `s`. -/
theorem ofFn_eq_flatten_blocks {α : Type*} (f : Fin (k * s) → α) :
    List.ofFn f =
      (List.ofFn fun i : Fin k => List.ofFn fun j : Fin s => f (finProdFinEquiv (i, j))).flatten := by
  rw [List.ofFn_mul]
  refine congrArg List.flatten (congrArg List.ofFn (funext fun i => congrArg List.ofFn
    (funext fun j => congrArg f (Fin.ext ?_))))
  change (i : ℕ) * s + j = _
  rw [finProdFinEquiv_val]
  ring
end
end MIPRE.CL

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.CL
open Cost.Data (chunk)
variable {k s : ℕ}
theorem _root_.solution (T : Fin k → Finset (Fin s)) :
    indicatorBits (blockSet finProdFinEquiv T) = (List.ofFn fun i => indicatorBits (T i)).flatten := by
  unfold indicatorBits
  rw [ofFn_eq_flatten_blocks]
  simp
end MIPRE.CL
