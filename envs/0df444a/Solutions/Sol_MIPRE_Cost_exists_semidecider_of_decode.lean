-- Prove2me | solution 1 for MIPRE.Cost.exists_semidecider_of_decode
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T20:42:03.683575+00:00
-- url     : https://prove2.me/submissions/1c26031c-6ac6-47f4-a5ec-8ec52ad59d61

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Halting/Semidecide.lean (solution of MIPRE.Cost.exists_semidecider_of_decode);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.PartrecBasis
import Mathlib.Computability.PartrecCode
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.RE
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
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Cost_Kleene
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec
import Definitions.Def_MIPRE_Foundations_Cost_FromPartrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Definitions.Def_MIPRE_Foundations_Cost_Partrec_B
import Definitions.Def_MIPRE_Foundations_Cost_Semidecide
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Numeric
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Theorems.Thm_MIPRE_Cost_Eval_deterministic
import Theorems.Thm_MIPRE_Cost_Eval_of_append_of_wellScoped

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Cost
theorem _root_.solution {α : Type*} [SizedEncoding α] [Primcodable α] [Inhabited α]
    (hdec : Primrec fun d : Data => (decode d : Option α))
    {p : α → Prop} (hp : REPred p) :
    ∃ S : Prog, S.WellScoped 1 ∧ ∀ a : α, Halts S (encode a) ↔ p a := by
  -- the predicate on bit strings: parse the string, decode it, fall back on `default`
  have hg : Computable fun y : BitStr => ((decode (Data.parse y) : Option α)).getD default :=
    (Primrec.option_getD.comp (hdec.comp Data.primrec_parse) (Primrec.const default)).to_comp
  have hre : REPred fun y : BitStr => p (((decode (Data.parse y) : Option α)).getD default) :=
    Partrec.comp hp hg
  obtain ⟨S', hws, hS'⟩ := exists_semidecider hre
  refine ⟨.let_ Prog.serProg S', ⟨Prog.serProg_wellScoped, hws.mono (by omega) _⟩, fun a => ?_⟩
  obtain ⟨s, -, hpre⟩ := Prog.serProg_runs (encode a)
  have hq : ((decode (Data.parse ((encode a : Data).toBitsPost)) : Option α)).getD default = a := by
    rw [Data.parse_toBitsPost, SizedEncoding.decode_encode]
    rfl
  have key : Halts (.let_ Prog.serProg S') (encode a) ↔
      Halts S' (encode ((encode a : Data).toBitsPost)) := by
    constructor
    · rintro ⟨r, t, h⟩
      cases h with
      | let_ h₁ h₂ =>
        obtain ⟨rfl, -⟩ := h₁.deterministic hpre
        exact ⟨r, _, Eval.of_append_of_wellScoped (env := [_]) (extra := [_]) h₂ hws⟩
    · rintro ⟨r, t, h⟩
      exact ⟨r, _, Eval.let_ hpre (Eval.append_of_wellScoped h hws _)⟩
  rw [key, hS', hq]
end MIPRE.Cost
