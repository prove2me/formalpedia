-- Prove2me | solution 1 for MIPRE.Cost.Machine.runs_of_runForD
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:45:23.037698+00:00
-- url     : https://prove2.me/submissions/57723c34-2aad-42e4-829a-3de759025b3e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/BoundedEval.lean (solution of MIPRE.Cost.Machine.runs_of_runForD);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_BoundedEval
import Theorems.Thm_MIPRE_Cost_Machine_halts_iff

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost.Machine
theorem _root_.solution {p : Prog} {x r : Data} {k : ℕ} (h : runForD (encode p) x k = some r) :
    ∃ t, p.Runs x r t := by
  rw [show runForD (encode p) x k =
      if isFinalB (stepData^[3 * k] (initData (encode p) x))
        then some (resultD (stepData^[3 * k] (initData (encode p) x))) else none from rfl,
    show initData (encode p) x = (⟨.ev p, [x], []⟩ : Cfg).toData from initData_eq p x,
    stepData_iterate] at h
  by_cases hfin : isFinalB (step^[3 * k] (⟨.ev p, [x], []⟩ : Cfg)).toData = true
  · obtain ⟨r', e, he⟩ := (isFinalD_toData _).1 ((isFinalB_iff _).1 hfin)
    rw [if_pos hfin, he, resultD_toData] at h
    exact Option.some.inj h ▸ (halts_iff p x r').2 ⟨3 * k, e, he⟩
  · rw [if_neg hfin] at h
    exact absurd h (by simp)
end MIPRE.Cost.Machine
