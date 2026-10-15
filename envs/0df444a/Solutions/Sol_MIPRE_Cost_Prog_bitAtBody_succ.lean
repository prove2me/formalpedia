-- Prove2me | solution 1 for MIPRE.Cost.Prog.bitAtBody_succ
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:48:10.113907+00:00
-- url     : https://prove2.me/submissions/01a2ad07-d016-4652-8f26-dc952888e7b9

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/BitQuery.lean (solution of MIPRE.Cost.Prog.bitAtBody_succ);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_BitQuery

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
theorem revOntoBody_wellScoped : revOntoBody.WellScoped 1 := by
  simp [revOntoBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem revOntoProg_wellScoped : revOntoProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, revOntoBody_wellScoped⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem isZeroBody_wellScoped : isZeroBody.WellScoped 1 := by
  simp [isZeroBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem isZeroProg_wellScoped : isZeroProg.WellScoped 1 :=
  ⟨Nat.zero_lt_one, isZeroBody_wellScoped⟩
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem decBody_wellScoped : decBody.WellScoped 1 := by
  simp [decBody, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
theorem decProg_wellScoped : decProg.WellScoped 1 :=
  ⟨⟨Nat.zero_lt_one, trivial⟩,
    ⟨⟨Nat.zero_lt_succ 1, decBody_wellScoped.mono (by omega) _⟩,
      revOntoProg_wellScoped.mono (by omega) _⟩⟩
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
theorem solution (b : Bool) (ys mb mb' : BitStr) (hz : mb.any id = true) (tz td : ℕ)
    (hzr : Eval [encode mb] isZeroProg (encode (mb.any id)) tz)
    (hd : Eval [encode mb] decProg (encode mb') td) :
    Eval [.cons (encode (b :: ys)) (encode mb)] bitAtBody
      (.cons (.cons .nil .nil) (.cons (encode ys) (encode mb')))
      (2 * (encode mb).size + tz + td + (encode ys).size + 14) := by
  rw [hz] at hzr
  have e := Eval.elim_cons (env := [Data.cons (encode (b :: ys)) (encode mb)]) (i := 0)
    (n := .nil) (a := encode (b :: ys)) (b := encode mb) (by simp)
    (Eval.elim_cons (i := 0) (n := .cons .nil (.const (.ofNat 2))) (a := encode b)
      (b := encode ys) (by simp)
      (Eval.let_ (callVar_eval (i := 3) isZeroProg_wellScoped (v := encode mb) (by simp) hzr)
        (Eval.elim_cons (i := 0) (n := .cons .nil (.var 1)) (a := .nil) (b := .nil) (by simp)
          (Eval.cons (Eval.cons (Eval.nil _) (Eval.nil _))
            (Eval.cons (Eval.var_of_get (i := 4) (v := encode ys) (by simp))
              (callVar_eval (i := 6) decProg_wellScoped (v := encode mb) (by simp) hd))))))
  exact e.cast_cost (by omega)
