-- Prove2me | solution 1 for MIPRE.Cost.Prog.ofCode_wellScoped
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:37:46.115224+00:00
-- url     : https://prove2.me/submissions/d65d08a0-fa10-4201-b214-1551861e25d2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/FromPartrec.lean (solution of MIPRE.Cost.Prog.ofCode_wellScoped);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.TuringMachine.Config
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Prog
open Turing.ToPartrec (Code)
theorem consTail_wellScoped : consTail.WellScoped 3 := by simp [consTail, WellScoped]
end MIPRE.Cost.Prog

namespace MIPRE.Cost.Prog
open Turing.ToPartrec (Code)
theorem fixBody_wellScoped {pf : Prog} (h : pf.WellScoped 1) : (fixBody pf).WellScoped 1 :=
  ⟨callVar_wellScoped (by decide) h, by simp [WellScoped]⟩
end MIPRE.Cost.Prog

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Prog
open Turing.ToPartrec (Code)
theorem solution : ∀ c : Code, (ofCode c).WellScoped 1
  | .zero' => by simp [ofCode, WellScoped]
  | .succ => by simp [ofCode, WellScoped]
  | .tail => by simp [ofCode, WellScoped]
  | .cons f fs =>
    ⟨solution f, callVar_wellScoped (by decide) (solution fs),
      consTail_wellScoped⟩
  | .comp f g => ⟨solution g, (solution f).mono (by omega) _⟩
  | .case f g =>
    ⟨by decide, callVar_wellScoped (by decide) (solution f), by decide,
      callVar_wellScoped (by decide) (solution f),
      ⟨by simp [WellScoped], by simp [WellScoped]⟩,
      callVar_wellScoped (by decide) (solution g)⟩
  | .fix f => ⟨by decide, fixBody_wellScoped (solution f)⟩
