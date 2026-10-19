-- Prove2me | solution 1 for MIPRE.TM.Interp.final_run
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:05:44.922981+00:00
-- url     : https://prove2.me/submissions/499c98dc-7dcd-4da3-9c10-6b1c8cfe2364

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Step.lean (solution of MIPRE.TM.Interp.final_run);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines
import Definitions.Def_MIPRE_TM_Interp_Repr
import Definitions.Def_MIPRE_TM_Interp_CopyTree
import Definitions.Def_MIPRE_TM_Interp_GetEnv
import Definitions.Def_MIPRE_TM_Interp_Desc
import Definitions.Def_MIPRE_TM_Interp_Step
import Theorems.Thm_MIPRE_TM_Interp_D_rewind

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Turing.MultiInputTM
section
open Relation
open MultiTapeTM (moveInputPos)
variable {i w : ℕ} {State Symbol : Type*}
variable {tm : MultiInputTM i w Symbol State}
variable {input : Fin i → List Symbol}
/-- Running `a + b` steps equals running `b` steps from the configuration reached after
`a`. -/
lemma configs_add (cfg : Cfg i w Symbol State input) (a b : ℕ) :
    tm.configs cfg (a + b) = tm.configs (tm.configs cfg a) b := by
  unfold configs
  rw [Nat.add_comm, Function.iterate_add_apply]
end
end Turing.MultiInputTM

namespace Turing.MultiInputTM
section
open Relation
open MultiTapeTM (moveInputPos)
open Cfg
variable {i w : ℕ} {State Symbol : Type*}
variable {tm : MultiInputTM i w Symbol State}
variable {input : Fin i → List Symbol}
/-- The output produced in `t + 1` steps is the output produced in `t` steps followed by
the symbol (optionally) emitted at step `t`. -/
lemma outputString_succ
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t : ℕ) :
    tm.outputString cfg (t + 1) =
      tm.outputString cfg t ++ (tm.outputSymbol (tm.configs cfg t)).toList := by
  simp [outputString, List.range_succ, List.flatMap_append]
end
end Turing.MultiInputTM

namespace Turing.MultiInputTM
section
open Relation
open MultiTapeTM (moveInputPos)
open Cfg
variable {i w : ℕ} {State Symbol : Type*}
variable {tm : MultiInputTM i w Symbol State}
variable {input : Fin i → List Symbol}
/-- From a halting configuration, a machine does not output anything. -/
lemma outputString_halt
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input)
    (h_halt : cfg.state = none)
    (t : ℕ) :
    tm.outputString cfg t = [] := by
  induction t with
  | zero => simp [outputString]
  | succ t ih => simp [outputString_succ, ih, h_halt]
end
end Turing.MultiInputTM

namespace Turing.MultiInputTM
section
open Relation
open MultiTapeTM (moveInputPos)
open Cfg
variable {i w : ℕ} {State Symbol : Type*}
variable {tm : MultiInputTM i w Symbol State}
variable {input : Fin i → List Symbol}
lemma outputString_add_eq_append
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) (t₁ t₂ : ℕ) :
    tm.outputString cfg (t₁ + t₂) =
      tm.outputString cfg t₁ ++ tm.outputString (tm.configs cfg t₁) t₂ := by
  induction t₂ with
  | zero => simp [outputString]
  | succ t ih =>
    rw [show (t₁ + (t + 1)) = (t₁ + t) + 1 by omega]
    simp [outputString_succ, ih, configs, ← Function.iterate_add_apply, Nat.add_comm]
end
end Turing.MultiInputTM

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
/-- One step of `U` is the action of the current instruction phase. -/
theorem step_eq (c : Cfg input) {q : Ctl} (hq : c.state = some q) :
    U.step c = applyAct (actOf q c) (resolve q.k q.pc (actOf q c).next) c := by
  unfold step
  rw [hq]
  dsimp only [U, actOf, applyAct]
  refine Cfg.ext rfl rfl (funext fun d => ?_) rfl
  dsimp only
  rcases h : ((execInstr (instrAt q.k q.pc) q.ph c.inputSymbols c.workTapeSymbols).works d).1 with
    _ | s <;> rfl
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem outputSymbol_eq (c : Cfg input) {q : Ctl} (hq : c.state = some q) :
    U.outputSymbol c = (actOf q c).out := by
  unfold outputSymbol
  rw [hq]
  rfl
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp.Reach
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem trans {c c' c'' : Cfg input} {n m : ℕ} {out out' : List Sym} (h : Reach c n c' out)
    (h' : Reach c' m c'' out') : Reach c (n + m) c'' (out ++ out') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨?_, ?_⟩
  · rw [configs_add, h1, h1']
  · rw [outputString_add_eq_append, h1, h2, h2']
end
end MIPRE.TM.Interp.Reach

namespace MIPRE.TM.Interp.Reach
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem single (c : Cfg input) : Reach c 1 (U.step c) (U.outputSymbol c).toList := by
  refine ⟨configs_succ_eq_step'.trans (by simp), ?_⟩
  rw [outputString_succ, outputString, List.range_zero, List.flatMap_nil, List.nil_append,
    configs_zero]
end
end MIPRE.TM.Interp.Reach

namespace MIPRE.TM.Interp.Reach
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem cast_out {c c' : Cfg input} {n : ℕ} {out out' : List Sym} (h : Reach c n c' out)
    (e : out = out') : Reach c n c' out' := e ▸ h
end
end MIPRE.TM.Interp.Reach

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem HaltsIn.of_reach {c c' : Cfg input} {n : ℕ} (h : Reach c n c' [])
    (h' : c'.state = none) : HaltsIn c n := by
  unfold HaltsIn; rw [h.1]; exact ⟨h', h.2⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem HaltsIn.mono {c : Cfg input} {n m : ℕ} (h : HaltsIn c n) (hnm : n ≤ m) : HaltsIn c m := by
  unfold HaltsIn at *
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  rw [configs_add, configs_of_halts _ h.1, outputString_add_eq_append, h.2,
    outputString_halt _ _ h.1]
  exact ⟨h.1, rfl⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
variable (a : Act) (q' : Option Ctl) (c : Cfg input)
theorem applyAct_workTapes_of_none (d : WT) (h : (a.works d).1 = none) :
    (applyAct a q' c).workTapes d = c.workTapes d := by
  simp [applyAct, h]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp.Act
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem mw_works_of_ne (a : Act) {t t' : WT} (h : t' ≠ t) (m : SignType) :
    (a.mw t m).works t' = a.works t' := by simp [mw, Function.update_of_ne h]
end
end MIPRE.TM.Interp.Act

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem resolve_adv (k : ProgId) (pc : Fin maxPc) (h : pc.val + 1 < maxPc) :
    resolve k pc .adv = next_ k pc h := by
  simp [resolve, next_, h]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp.Untouched
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem mono {c c' : Cfg input} {SI SI' : List IT} {SW SW' : List WT} (h : Untouched c c' SI SW)
    (hI : ∀ j ∈ SI, j ∈ SI') (hW : ∀ d ∈ SW, d ∈ SW') : Untouched c c' SI' SW' :=
  ⟨fun j hj => h.1 j fun hmem => hj (hI j hmem), fun d hd => h.2 d fun hmem => hd (hW d hmem)⟩
end
end MIPRE.TM.Interp.Untouched

namespace MIPRE.TM.Interp.Untouched
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem tapes {c c' : Cfg input} {SI : List IT} {SW : List WT} (h : Untouched c c' SI SW) {d : WT}
    (hd : d ∉ SW) : c'.workTapes d = c.workTapes d := (h.2 d hd).1
end
end MIPRE.TM.Interp.Untouched

namespace MIPRE.TM.Interp.Untouched
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem pos {c c' : Cfg input} {SI : List IT} {SW : List WT} (h : Untouched c c' SI SW) {d : WT}
    (hd : d ∉ SW) : c'.workTapePos d = c.workTapePos d := (h.2 d hd).2
end
end MIPRE.TM.Interp.Untouched

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
/-- The symbol under the head of work tape `t`. -/
theorem workTapeSymbols_eq (c : Cfg input) (t : WT) :
    c.workTapeSymbols t = c.workTapes t (c.workTapePos t) := rfl
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
/-- One step at `(k, pc, ph)` executing the instruction `ins` there. -/
theorem step_instr {c : Cfg input} {k : ProgId} {pc : Fin maxPc} {ph : Phase}
    (hq : c.state = some ⟨k, pc, ph⟩) {ins : Instr} (hins : instrAt k pc = ins) :
    let a := execInstr ins ph c.inputSymbols c.workTapeSymbols
    Reach c 1 (applyAct a (resolve k pc a.next) c) a.out.toList := by
  have := Reach.single c
  rwa [step_eq c hq, outputSymbol_eq c hq, actOf, hins] at this
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem untouched_applyAct {a : Act} {SI : List IT} {SW : List WT} (h : a.Within SI SW)
    (q' : Option Ctl) (c : Cfg input) : Untouched c (applyAct a q' c) SI SW := by
  refine ⟨fun j hj => ?_, fun d hd => ?_⟩
  · simp [applyAct, h.1 j hj]
  · have := h.2 d hd
    refine ⟨?_, ?_⟩
    · rw [applyAct_workTapes_of_none _ _ _ _ (by rw [this])]
    · rw [applyAct_workTapePos, this]; simp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem exec_move {k : ProgId} {pc : Fin maxPc} {t : WT} {dir : Bool}
    (hins : instrAt k pc = .move t dir) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧
      c'.workTapePos t = c.workTapePos t + (if dir then 1 else -1) := by
  have h := step_instr hq hins
  simp only [execInstr] at h
  refine ⟨_, h, ?_, ?_, ?_, ?_⟩
  · simp [resolve_adv k pc hpc]
  · refine untouched_applyAct ⟨fun j _ => rfl, fun d hd => ?_⟩ _ _
    have : d ≠ t := by simpa using hd
    simp [Act.mw_works_of_ne _ this]
  · rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
  · cases dir <;> simp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem exec_branch_taken {k : ProgId} {pc : Fin maxPc} {t : WT} {s : Option Sym} {target : ProgId}
    (hins : instrAt k pc = .branch t s target) (c : Cfg input) (hq : c.state = at_ k pc)
    (hs : c.workTapes t (c.workTapePos t) = s) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = at_ target ⟨0, by decide⟩ ∧ Untouched c c' [] [] ∧
      ∀ d, c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d := by
  have h := step_instr hq hins
  simp only [execInstr, workTapeSymbols_eq, hs, if_true, Act.base_out, Option.toList_none,
    Act.base_next, resolve_jmp] at h
  refine ⟨_, h, rfl, untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _, fun d => ?_⟩
  exact ⟨by rw [applyAct_workTapes_of_none _ _ _ d (by simp)], by simp⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem exec_branch_not {k : ProgId} {pc : Fin maxPc} {t : WT} {s : Option Sym} {target : ProgId}
    (hins : instrAt k pc = .branch t s target) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) (hs : c.workTapes t (c.workTapePos t) ≠ s) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [] ∧
      ∀ d, c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d := by
  have h := step_instr hq hins
  simp only [execInstr, workTapeSymbols_eq, hs, if_false, Act.base_out, Option.toList_none,
    Act.base_next] at h
  refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _,
    fun d => ?_⟩
  exact ⟨by rw [applyAct_workTapes_of_none _ _ _ d (by simp)], by simp⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem exec_emit {k : ProgId} {pc : Fin maxPc} {s : Sym}
    (hins : instrAt k pc = .emit s) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [s] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [] ∧
      ∀ d, c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d := by
  have h := step_instr hq hins
  simp only [execInstr, Act.emit_out, Option.toList_some, Act.emit_next, Act.base_next] at h
  refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _,
    fun d => ?_⟩
  exact ⟨by rw [applyAct_workTapes_of_none _ _ _ d (by simp)], by simp⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem exec_halt {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .halt) (c : Cfg input)
    (hq : c.state = at_ k pc) : HaltsIn c 1 := by
  have h := step_instr hq hins
  simp only [execInstr, Act.base_out, Option.toList_none, Act.base_next, resolve_halt] at h
  exact HaltsIn.of_reach h rfl
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open MIPRE.Cost MIPRE.Cost.Machine
theorem S_cons (a b : Data) : S (.cons a b) = .one :: (S a ++ S b) := by
  simp [S, Data.toBits]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
theorem length_S_ofNat (i : ℕ) : (S (Data.ofNat i)).length = 2 * i + 1 := by simp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
theorem overwrite_append (a l w : List Sym) :
    overwrite (a ++ l) a.length w = a ++ w ++ l.drop w.length := by
  simp only [overwrite, List.take_left]
  rw [← List.drop_drop, List.drop_left]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
theorem overwrite_append' (a l w : List Sym) {p : ℕ} (hp : p = a.length) :
    overwrite (a ++ l) p w = a ++ w ++ l.drop w.length := by
  subst hp; exact overwrite_append a l w
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
theorem overwrite_append_nil (a w : List Sym) {p : ℕ} (hp : p = a.length) :
    overwrite a p w = a ++ w := by
  have := overwrite_append' a [] w hp
  simpa using this
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp.TapeIs
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
theorem holds (h : TapeIs τ pos s) : Holds τ 0 s.l := h.1
end
end MIPRE.TM.Interp.TapeIs

namespace MIPRE.TM.Interp.TapeIs
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
theorem before (h : TapeIs τ pos s) (q : ℤ) (hq : q < 0) : τ q = none := h.2.1 q hq
end
end MIPRE.TM.Interp.TapeIs

namespace MIPRE.TM.Interp.TapeIs
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
theorem beyond (h : TapeIs τ pos s) (q : ℤ) (hq : (s.l.length : ℤ) ≤ q) : τ q = none := h.2.2.1 q hq
end
end MIPRE.TM.Interp.TapeIs

namespace MIPRE.TM.Interp.TapeIs
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
theorem pos_eq (h : TapeIs τ pos s) : pos = s.p := h.2.2.2
end
end MIPRE.TM.Interp.TapeIs

namespace MIPRE.TM.Interp.TapeIs
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
/-- The cell `n`. -/
theorem read (h : TapeIs τ pos s) (n : ℕ) : τ n = s.l[n]? := by
  by_cases hn : n < s.l.length
  · rw [List.getElem?_eq_getElem hn]
    have := h.holds n hn
    rwa [zero_add] at this
  · rw [List.getElem?_eq_none (by omega)]
    exact h.beyond n (by omega)
end
end MIPRE.TM.Interp.TapeIs

namespace MIPRE.TM.Interp.TapeIs
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
/-- The cell under the head. -/
theorem read_pos (h : TapeIs τ pos s) : τ pos = s.l[s.p]? := by
  rw [h.pos_eq]; exact h.read s.p
end
end MIPRE.TM.Interp.TapeIs

namespace MIPRE.TM.Interp.TapeIs
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
/-- Same tape, another head position. -/
theorem of_same {l : List Sym} {p : ℕ} (h : TapeIs τ pos ⟨l, p⟩) {τ' : Tape} {pos' : ℤ} {p' : ℕ}
    (hτ : τ' = τ) (hpos : pos' = p') : TapeIs τ' pos' ⟨l, p'⟩ :=
  ⟨hτ ▸ h.holds, fun q hq => hτ ▸ h.before q hq, fun q hq => hτ ▸ h.beyond q hq, hpos⟩
end
end MIPRE.TM.Interp.TapeIs

namespace MIPRE.TM.Interp.Desc
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {c : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}
theorem state (h : Desc c q ds) : c.state = q := h.1
end
end MIPRE.TM.Interp.Desc

namespace MIPRE.TM.Interp.Desc
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {c : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}
theorem tape (h : Desc c q ds) (t : WT) : TapeIs (c.workTapes t) (c.workTapePos t) (ds t) := h.2 t
end
end MIPRE.TM.Interp.Desc

namespace MIPRE.TM.Interp.Desc
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {c : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}
theorem pos (h : Desc c q ds) (t : WT) : c.workTapePos t = (ds t).p := (h.2 t).pos_eq
end
end MIPRE.TM.Interp.Desc

namespace MIPRE.TM.Interp.Desc
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {c : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}
theorem read (h : Desc c q ds) (t : WT) : c.workTapes t (c.workTapePos t) = (ds t).l[(ds t).p]? :=
  (h.2 t).read_pos
end
end MIPRE.TM.Interp.Desc

namespace MIPRE.TM.Interp.Desc
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {c : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}
/-- A run touching only the tapes in `SW`, whose new descriptions are given. -/
theorem of_untouched (h : Desc c q ds) {c' : Cfg input} {SW : List WT}
    (hu : Untouched c c' [] SW) {q' : Option Ctl} (hq' : c'.state = q') {ds' : WT → TapeSt}
    (hT : ∀ t ∈ SW, TapeIs (c'.workTapes t) (c'.workTapePos t) (ds' t))
    (hS : ∀ t, t ∉ SW → ds' t = ds t) : Desc c' q' ds' := by
  refine ⟨hq', fun t => ?_⟩
  by_cases ht : t ∈ SW
  · exact hT t ht
  · rw [hS t ht, (hu.tapes ht), (hu.pos ht)]
    exact h.tape t
end
end MIPRE.TM.Interp.Desc

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}
theorem D_move_right {t : WT} (hins : instrAt k pc = .move t true) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l, (ds t).p + 1⟩) := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_move hins hpc c hd.state
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    exact (hd.tape t').of_same htape (by rw [hpos, hd.pos]; simp)
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}
theorem D_branch_not {t : WT} {s : Option Sym} {target : ProgId}
    (hins : instrAt k pc = .branch t s target) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hs : (ds t).l[(ds t).p]? ≠ s) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (next_ k pc hpc) ds := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_branch_not hins hpc c hd.state (by rw [hd.read]; exact hs)
  exact ⟨c', hr, hd.of_untouched (SW := []) (hu.mono (by simp) (by simp)) hst (by simp)
    (fun _ _ => rfl)⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
/-- The representation, as an explicit description (the scratch tape as it is). -/
theorem RepOf.eq {ds : WT → TapeSt} {m : Machine.Cfg} {r pC pK : ℕ} (h : RepOf ds m r pC pK) :
    ∃ g, ds = Function.update (Function.update (Function.update (Function.update (Function.update ds
      C ⟨ctrlRepr m.ctrl ++ g, pC⟩) E ⟨envRepr m.env, (envRepr m.env).length⟩)
      K ⟨kontRepr m.kont, pK⟩) CNT ⟨[], 0⟩) BUD ⟨List.replicate r .one, r⟩ := by
  obtain ⟨g, hC⟩ := h.ctrl
  refine ⟨g, funext fun t => ?_⟩
  fin_cases t
  · simpa using hC
  · simpa using h.env
  · simpa using h.kont
  · simp
  · simpa using h.cnt
  · simpa using h.bud
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem ctrlRepr_var (i : ℕ) :
    ctrlRepr (.ev (.var i)) = .zero :: .one :: .zero :: S (Data.ofNat i) := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem ctrlRepr_nil :
    ctrlRepr (.ev .nil) = [.zero, .one, .one, .zero, .zero, .zero] := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem ctrlRepr_cons (h t : Prog) :
    ctrlRepr (.ev (.cons h t)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .zero :: .one :: (S h.toData ++ S t.toData) := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem ctrlRepr_elim (i : ℕ) (n c : Prog) :
    ctrlRepr (.ev (.elim i n c)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .zero :: .one ::
        (S (Data.ofNat i) ++ .one :: (S n.toData ++ S c.toData)) := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem ctrlRepr_let (e b : Prog) :
    ctrlRepr (.ev (.let_ e b)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .zero ::
        .one :: (S e.toData ++ S b.toData) := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem ctrlRepr_loop (b : Prog) :
    ctrlRepr (.ev (.loop b)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one ::
        .zero :: .zero :: S b.toData := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem ctrlRepr_const (d : Data) :
    ctrlRepr (.ev (.const d)) =
      .zero :: .one :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one :: .zero :: .one ::
        .zero :: .one :: .zero :: .zero :: S d := by
  simp [ctrlRepr, Prog.toData, S_cons, Data.ofNat]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem ctrlRepr_ret (v : Data) : ctrlRepr (.ret v) = .one :: S v := rfl
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem overwrite_cons_one_add (a : Sym) (l : List Sym) (p : ℕ) (w : List Sym) :
    overwrite (a :: l) (1 + p) w = a :: overwrite l p w := by
  rw [Nat.add_comm]; exact overwrite_cons_succ a l p w
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem overwrite_append_nil' (a w : List Sym) {p : ℕ} (hp : p = a.length) :
    overwrite a p w = a ++ w := overwrite_append_nil a w hp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem F_move_right {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {l : List Sym} {p : ℕ}
    (hins : instrAt k pc = .move C true) (hpc : pc.val + 1 < maxPc) (h : CDesc c (at_ k pc) ⟨l, p⟩) :
    ∃ c', Reach c 1 c' [] ∧ CDesc c' (next_ k pc hpc) ⟨l, p + 1⟩ := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_move hins hpc c h.1
  exact ⟨c', hr, hs, h.2.of_same htape (by rw [hpos, h.2.pos_eq]; simp)⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem F_branch_taken {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {l : List Sym} {p : ℕ}
    {s : Option Sym} {target : ProgId} (hins : instrAt k pc = .branch C s target)
    (h : CDesc c (at_ k pc) ⟨l, p⟩) (hs : l[p]? = s) :
    ∃ c', Reach c 1 c' [] ∧ CDesc c' (at_ target ⟨0, by decide⟩) ⟨l, p⟩ := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_branch_taken hins c h.1 (by rw [h.2.read_pos]; exact hs)
  exact ⟨c', hr, hst, h.2.of_same (hall C).1 ((hall C).2.trans h.2.pos_eq)⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem F_branch_not {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {l : List Sym} {p : ℕ}
    {s : Option Sym} {target : ProgId} (hins : instrAt k pc = .branch C s target)
    (hpc : pc.val + 1 < maxPc) (h : CDesc c (at_ k pc) ⟨l, p⟩) (hs : l[p]? ≠ s) :
    ∃ c', Reach c 1 c' [] ∧ CDesc c' (next_ k pc hpc) ⟨l, p⟩ := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_branch_not hins hpc c h.1 (by rw [h.2.read_pos]; exact hs)
  exact ⟨c', hr, hst, h.2.of_same (hall C).1 ((hall C).2.trans h.2.pos_eq)⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem F_emit {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {l : List Sym} {p : ℕ} {s : Sym}
    (hins : instrAt k pc = .emit s) (hpc : pc.val + 1 < maxPc) (h : CDesc c (at_ k pc) ⟨l, p⟩) :
    ∃ c', Reach c 1 c' [s] ∧ CDesc c' (next_ k pc hpc) ⟨l, p⟩ := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_emit hins hpc c h.1
  exact ⟨c', hr, hst, h.2.of_same (hall C).1 ((hall C).2.trans h.2.pos_eq)⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem F_halt {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {s : TapeSt}
    (hins : instrAt k pc = .halt) (h : CDesc c (at_ k pc) s) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = none :=
  have := exec_halt hins c h.1
  ⟨_, ⟨rfl, this.2⟩, this.1⟩
end
end MIPRE.TM.Interp

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem _root_.solution {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {v : Data} {env : Env} {r : ℕ}
    (hr : RepOf ds ⟨.ret v, env, []⟩ r (ctrlRepr (.ret v)).length (kontRepr []).length) :
    (v = Data.ofBool true → ∃ n ≤ v.size + 16, AcceptsFrom c n) ∧
    (v ≠ Data.ofBool true → HaltsIn c (v.size + 16)) := by
  obtain ⟨g, hds⟩ := hr.eq
  rw [hds] at hd
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_rewind rfl (by decide) hd (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₁ hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_branch_not rfl (by decide) hd₁ (by simp)
  obtain ⟨c₃, hr₃, hd₃⟩ := D_move_right rfl (by decide) hd₂
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₃
  -- the stack is empty: the head of `K` moves before the tape and the branch to `final` is taken
  obtain ⟨c₄, hr₄, hs₄, hu₄, hK₄, hKp₄⟩ := exec_move (t := K) (dir := false) rfl (by decide) c₃ hd₃.state
  have hread : c₄.workTapes K (c₄.workTapePos K) = none := by
    rw [hK₄, hKp₄, hd₃.pos K]
    exact (hd₃.tape K).before _ (by simp)
  obtain ⟨c₅, hr₅, hs₅, hu₅, hall₅⟩ := exec_branch_taken (t := K) (s := none) (target := .final) rfl c₄
    hs₄ hread
  have hC₅ : CDesc c₅ (at_ .final 0) ⟨.one :: (S v ++ g), 1⟩ := by
    refine ⟨hs₅, ?_⟩
    have := hd₃.tape C
    simp only [Function.update_self] at this
    exact this.of_same ((hall₅ C).1.trans (hu₄.tapes (d := C) (by decide)))
      (((hall₅ C).2.trans (hu₄.pos (d := C) (by decide))).trans (by rw [hd₃.pos C]; rfl))
  have hR := hr₁.trans hr₂
  have hR := hR.trans hr₃
  have hR := hR.trans hr₄
  have hR := hR.trans hr₅
  have hR : Reach c _ c₅ [] := hR.cast_out (by simp)
  -- the final program reads the bits of `v`
  cases v with
  | nil =>
    refine ⟨fun h => by simp [Data.ofBool] at h, fun _ => ?_⟩
    obtain ⟨c₆, hr₆, hd₆⟩ := F_branch_not rfl (by decide) hC₅ (by simp)
    obtain ⟨c₇, hr₇, hs₇⟩ := F_halt rfl hd₆
    exact (HaltsIn.of_reach ((hR.trans hr₆).trans hr₇ |>.cast_out (by simp)) hs₇).mono (by simp)
  | cons a b =>
    obtain ⟨c₆, hr₆, hd₆⟩ := F_branch_taken rfl hC₅ (by simp [S_cons])
    obtain ⟨c₇, hr₇, hd₇⟩ := F_move_right rfl (by decide) hd₆
    cases a with
    | cons a₁ a₂ =>
      refine ⟨fun h => by simp [Data.ofBool] at h, fun _ => ?_⟩
      obtain ⟨c₈, hr₈, hd₈⟩ := F_branch_not rfl (by decide) hd₇ (by simp [S_cons])
      obtain ⟨c₉, hr₉, hs₉⟩ := F_halt rfl hd₈
      exact (HaltsIn.of_reach ((((hR.trans hr₆).trans hr₇).trans hr₈).trans hr₉ |>.cast_out (by simp))
        hs₉).mono (by simp [Data.size_cons] <;> omega)
    | nil =>
      obtain ⟨c₈, hr₈, hd₈⟩ := F_branch_taken rfl hd₇ (by simp [S_cons])
      obtain ⟨c₉, hr₉, hd₉⟩ := F_move_right rfl (by decide) hd₈
      cases b with
      | cons b₁ b₂ =>
        refine ⟨fun h => by simp [Data.ofBool] at h, fun _ => ?_⟩
        obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := F_branch_not rfl (by decide) hd₉ (by simp [S_cons])
        obtain ⟨c₁₁, hr₁₁, hs₁₁⟩ := F_halt rfl hd₁₀
        exact (HaltsIn.of_reach ((((((hR.trans hr₆).trans hr₇).trans hr₈).trans hr₉).trans hr₁₀).trans
          hr₁₁ |>.cast_out (by simp)) hs₁₁).mono (by simp [Data.size_cons] <;> omega)
      | nil =>
        refine ⟨fun _ => ?_, fun h => absurd rfl h⟩
        obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := F_branch_taken rfl hd₉ (by simp [S_cons])
        obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := F_emit rfl (by decide) hd₁₀
        obtain ⟨c₁₂, hr₁₂, hs₁₂⟩ := F_halt rfl hd₁₁
        refine ⟨_, ?_, c₁₂, ((((((hR.trans hr₆).trans hr₇).trans hr₈).trans hr₉).trans
          hr₁₀).trans hr₁₁).trans hr₁₂ |>.cast_out (by simp), hs₁₂⟩
        simp [Data.size_cons] <;> omega
end MIPRE.TM.Interp
