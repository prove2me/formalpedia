-- Prove2me | solution 1 for MIPRE.TM.Interp.case_retLoopCont
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:05:43.704033+00:00
-- url     : https://prove2.me/submissions/60a872f5-1df6-4741-abcf-947d829356c5

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Step.lean (solution of MIPRE.TM.Interp.case_retLoopCont);
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
import Theorems.Thm_MIPRE_TM_Interp_D_copyTree
import Theorems.Thm_MIPRE_TM_Interp_D_copyUntil
import Theorems.Thm_MIPRE_TM_Interp_D_eraseRight
import Theorems.Thm_MIPRE_TM_Interp_D_leftToMarker
import Theorems.Thm_MIPRE_TM_Interp_D_popBack
import Theorems.Thm_MIPRE_TM_Interp_D_popBack_empty
import Theorems.Thm_MIPRE_TM_Interp_D_rewind
import Theorems.Thm_MIPRE_TM_Interp_D_skipTree
import Theorems.Thm_MIPRE_TM_Interp_D_toEnd
import Theorems.Thm_MIPRE_TM_Interp_D_write
import Theorems.Thm_MIPRE_TM_Interp_mem_frameBody

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
theorem exec_jump {k : ProgId} {pc : Fin maxPc} {target : ProgId}
    (hins : instrAt k pc = .jump target) (c : Cfg input) (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = at_ target ⟨0, by decide⟩ ∧ Untouched c c' [] [] ∧
      ∀ d, c'.workTapes d = c.workTapes d ∧ c'.workTapePos d = c.workTapePos d := by
  have h := step_instr hq hins
  simp only [execInstr, Act.base_out, Option.toList_none, Act.base_next, resolve_jmp] at h
  refine ⟨_, h, rfl, untouched_applyAct ⟨fun j _ => rfl, fun d _ => rfl⟩ _ _, fun d => ?_⟩
  exact ⟨by rw [applyAct_workTapes_of_none _ _ _ d (by simp)], by simp⟩
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
open MIPRE.Cost MIPRE.Cost.Machine
/-- The symbols of a value are bits. -/
theorem mem_S (v : Data) : ∀ s ∈ S v, s = .zero ∨ s = .one := by
  intro s hs
  simp only [S, bits, List.mem_map] at hs
  obtain ⟨b, -, rfl⟩ := hs
  cases b <;> simp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open MIPRE.Cost MIPRE.Cost.Machine
/-- No `$` and no `¶` in an environment. -/
theorem mem_envRepr (env : Env) : ∀ s ∈ envRepr env, s ≠ .fr ∧ s ≠ .en := by
  induction env with
  | nil => simp
  | cons v env ih =>
    intro s hs
    simp only [envRepr_cons, List.mem_append, List.mem_singleton] at hs
    rcases hs with (hs | hs) | rfl
    · exact ih s hs
    · rcases mem_S v s hs with rfl | rfl <;> simp
    · simp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open MIPRE.Cost MIPRE.Cost.Machine
theorem frameRepr_eq (f : Frame) : frameRepr f = frameBody f ++ [.fr] := by
  cases f <;> simp [frameRepr, frameBody]
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
theorem cast (h : Desc c q ds) {q' : Option Ctl} {ds' : WT → TapeSt} (hq : q = q')
    (hds : ds = ds') : Desc c q' ds' := hq ▸ hds ▸ h
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
theorem D_move_left {t : WT} (hins : instrAt k pc = .move t false) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : 1 ≤ (ds t).p) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l, (ds t).p - 1⟩) := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_move hins hpc c hd.state
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    exact (hd.tape t').of_same htape (by rw [hpos, hd.pos]; simp; omega)
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
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}
theorem D_jump {target : ProgId} (hins : instrAt k pc = .jump target) (hd : Desc c (at_ k pc) ds) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (at_ target ⟨0, by decide⟩) ds := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_jump hins c hd.state
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
theorem kontRepr_nil_or_fr (k : List Frame) :
    kontRepr k = [] ∨ ∃ l₀, kontRepr k = l₀ ++ [.fr] := by
  cases k with
  | nil => exact Or.inl rfl
  | cons f k => exact Or.inr ⟨kontRepr k ++ frameBody f, by simp [frameRepr_eq]⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem envRepr_nil_or_sep (env : Env) :
    envRepr env = [] ∨ ∃ l₀, envRepr env = l₀ ++ [.sep] := by
  cases env with
  | nil => exact Or.inl rfl
  | cons v env => exact Or.inr ⟨envRepr env ++ S v, by simp⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem mem_envRepr_ne_fr (env : Env) : ∀ s ∈ envRepr env, some s ≠ some Sym.fr :=
  fun s hs h => (mem_envRepr env s hs).1 (Option.some_injective _ h)
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem mem_envRepr_ne_en (env : Env) : ∀ s ∈ envRepr env, s ≠ Sym.en :=
  fun s hs => (mem_envRepr env s hs).2
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem frameBody_ne_fr (f : Frame) : ∀ s ∈ frameBody f, s ≠ Sym.fr := mem_frameBody f
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem frameBody_loop1 (b : Prog) (env : Env) :
    frameBody (.loop1 b env) = .one :: .one :: (S b.toData ++ [.en] ++ envRepr env) := by
  simp [frameBody]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem kontRepr_cons' (f : Frame) (k : List Frame) :
    kontRepr (f :: k) = kontRepr k ++ frameBody f ++ [.fr] := by
  simp [frameRepr_eq]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem D_popEnv {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}
    (hins : instrAt k pc = .popBack .sep E) (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds)
    {env' : Env} (hE : ds E = ⟨envRepr env', (envRepr env').length⟩) :
    ∃ n ≤ (envRepr env').length + 3, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc)
        (Function.update ds E ⟨envRepr env'.tail, (envRepr env'.tail).length⟩) := by
  cases env' with
  | nil =>
    obtain ⟨c', hr, hd'⟩ := D_popBack_empty hins hpc hd (by simp [hE]) (by simp [hE])
    refine ⟨2, by simp, c', hr, hd'.cast rfl ?_⟩
    rw [show (⟨envRepr [].tail, (envRepr [].tail).length⟩ : TapeSt) = ds E by simp [hE]]
    exact (Function.update_eq_self E ds).symm
  | cons e₁ rest =>
    obtain ⟨c', hr, hd'⟩ := D_popBack hins hpc hd (l₁ := envRepr rest) (w := S e₁) (a := .sep)
      (by simp [hE]) (by simp [hE])
      (fun s hs h => by subst h; rcases mem_S e₁ _ hs with h | h <;> simp at h)
      (envRepr_nil_or_sep rest)
    exact ⟨_, by simp; omega, c', hr, hd'⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem drop_env_ne_fr (env : Env) (n : ℕ) : ∀ s ∈ (envRepr env).drop n, s ≠ Sym.fr :=
  fun s hs => (mem_envRepr env s (List.mem_of_mem_drop hs)).1
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
theorem _root_.solution {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .retLoop1 0) ds)
    {y z v' : Data} {b : Prog} {env env' : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ret (.cons (.cons y z) v'), env, .loop1 b env' :: k⟩ r 1
      ((kontRepr k).length + 1)) :
    PreTo c (caseBound ⟨.ret (.cons (.cons y z) v'), env, .loop1 b env' :: k⟩ (ds X).l.length)
      (at_ .retLoopCont 29) ⟨.ev b, v' :: env'.tail, .loop1 b (v' :: env'.tail) :: k⟩ r
      (ctrlRepr (.ev b)).length (kontRepr (.loop1 b (v' :: env'.tail) :: k)).length
      ((ds X).l.length + sz ⟨.ret (.cons (.cons y z) v'), env, .loop1 b env' :: k⟩) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  simp only [kontRepr_cons', frameBody_loop1] at hd
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_branch_not rfl (by decide) hd (by simp)
  obtain ⟨c₂, hr₂, hd₂⟩ := D_move_right rfl (by decide) hd₁
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_branch_not rfl (by decide) hd₂ (by simp)
  obtain ⟨c₄, hr₄, hd₄⟩ := D_jump rfl hd₃
  -- `retLoopCont`
  obtain ⟨n₅, hn₅, c₅, hr₅, hd₅⟩ := D_skipTree rfl (by decide) (by decide) hd₄ (by simp <;> omega)
    (v := .cons y z) (l₁ := [.one, .one]) (l₂ := S v' ++ g) (by simp [S_cons, List.append_assoc])
    (by simp <;> omega)
  simp only [Data.size_cons] at hn₅
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_rewind rfl (by decide) hd₅ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₆ hd₆
  obtain ⟨n₇, hn₇, c₇, hr₇, hd₇⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide) hd₆
    (by simp <;> omega) (v := v') (l₁ := [.one, .one] ++ S (.cons y z)) (l₂ := g)
    (by simp [S_cons, List.append_assoc]) (by simp <;> omega) (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₇
  obtain ⟨c₈, hr₈, hd₈⟩ := D_move_right rfl (by decide) hd₇
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₈
  obtain ⟨n₉, hn₉, c₉, hr₉, hd₉⟩ := D_skipTree rfl (by decide) (by decide) hd₈ (by simp <;> omega)
    (v := b.toData) (l₁ := kontRepr k ++ [.one, .one]) (l₂ := [.en] ++ envRepr env' ++ [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₉
  obtain ⟨c₁₀, hr₁₀, hd₁₀⟩ := D_move_right rfl (by decide) hd₉
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁⟩ := D_rewind rfl (by decide) hd₁₀ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₁₁ hd₁₁
  obtain ⟨c₁₂, hr₁₂, hd₁₂⟩ := D_copyUntil rfl (by decide) (by decide) hd₁₁
    (l₁ := kontRepr k ++ [.one, .one] ++ S b.toData ++ [.en]) (w := envRepr env') (l₂ := [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega) (mem_envRepr_ne_fr env') rfl (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₁₂
  obtain ⟨c₁₃, hr₁₃, hd₁₃⟩ := D_eraseRight rfl (by decide) hd₁₂ (by simp <;> omega)
    (by simp only [Function.update_self, List.drop_left']; exact drop_env_ne_fr env _)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₁₃ hd₁₃
  simp only [List.take_left'] at hd₁₃
  obtain ⟨n₁₄, hn₁₄, c₁₄, hr₁₄, hd₁₄⟩ := D_popEnv rfl (by decide) hd₁₃ (env' := env') (by simp)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₁₄
  obtain ⟨c₁₅, hr₁₅, hd₁₅⟩ := D_rewind rfl (by decide) hd₁₄ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₁₅ hd₁₅
  obtain ⟨n₁₆, hn₁₆, c₁₆, hr₁₆, hd₁₆⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₁₅ (by simp <;> omega) (v := v') (l₁ := []) (l₂ := (ds X).l.drop v'.size) (by simp <;> omega)
    (by simp <;> omega) (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₁₆
  obtain ⟨c₁₇, hr₁₇, hd₁₇⟩ := D_write rfl (by decide) hd₁₆ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₁₇
  obtain ⟨c₁₈, hr₁₈, hd₁₈⟩ := D_move_right rfl (by decide) hd₁₇
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₁₈
  obtain ⟨c₁₉, hr₁₉, hd₁₉⟩ := D_popBack rfl (by decide) hd₁₈
    (l₁ := kontRepr k ++ [.one, .one] ++ S b.toData ++ [.en]) (w := envRepr env') (a := .fr)
    (by simp [List.append_assoc]) (by simp <;> omega) (mem_envRepr_ne_en env')
    (Or.inr ⟨kontRepr k ++ [.one, .one] ++ S b.toData, by simp⟩)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₁₉
  obtain ⟨c₂₀, hr₂₀, hd₂₀⟩ := D_rewind rfl (by decide) hd₁₉ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₂₀ hd₂₀
  obtain ⟨c₂₁, hr₂₁, hd₂₁⟩ := D_copyUntil rfl (by decide) (by decide) hd₂₀ (l₁ := [])
    (w := envRepr env'.tail ++ S v' ++ [.sep]) (l₂ := []) (by simp [List.append_assoc])
    (by simp <;> omega) (fun _ _ => Option.some_ne_none _) rfl (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₂₁
  obtain ⟨c₂₂, hr₂₂, hd₂₂⟩ := D_write rfl (by decide) hd₂₁ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₂₂
  obtain ⟨c₂₃, hr₂₃, hd₂₃⟩ := D_move_left rfl (by decide) hd₂₂ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₂₃
  obtain ⟨c₂₄, hr₂₄, hd₂₄⟩ := D_leftToMarker rfl (by decide) hd₂₃ (l₁ := kontRepr k)
    (w := .one :: .one :: (S b.toData ++ [.en] ++ envRepr (v' :: env'.tail))) (l₂ := [.fr])
    (by simp [List.append_assoc]) (by simp <;> omega)
    (by simpa [frameBody_loop1] using frameBody_ne_fr (.loop1 b (v' :: env'.tail)))
    (kontRepr_nil_or_fr k)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₂₄
  obtain ⟨c₂₅, hr₂₅, hd₂₅⟩ := D_move_right rfl (by decide) hd₂₄
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₂₅
  obtain ⟨c₂₆, hr₂₆, hd₂₆⟩ := D_move_right rfl (by decide) hd₂₅
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₂₆
  obtain ⟨c₂₇, hr₂₇, hd₂₇⟩ := D_rewind rfl (by decide) hd₂₆ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₂₇ hd₂₇
  obtain ⟨n₂₈, hn₂₈, c₂₈, hr₂₈, hd₂₈⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₂₇ (by simp <;> omega) (v := b.toData) (l₁ := kontRepr k ++ [.one, .one])
    (l₂ := [.en] ++ (envRepr env'.tail ++ S v' ++ [.sep]) ++ [.fr]) (by simp [List.append_assoc])
    (by simp <;> omega) (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₂₈
  obtain ⟨c₂₉, hr₂₉, hd₂₉⟩ := D_rewind rfl (by decide) hd₂₈ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₂₉ hd₂₉
  obtain ⟨c₃₀, hr₃₀, hd₃₀⟩ := D_write rfl (by decide) hd₂₉ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₃₀
  obtain ⟨c₃₁, hr₃₁, hd₃₁⟩ := D_rewind rfl (by decide) hd₃₀ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₃₁ hd₃₁
  obtain ⟨n₃₂, hn₃₂, c₃₂, hr₃₂, hd₃₂⟩ := D_copyTree rfl (by decide) (by decide) (by decide) (by decide)
    hd₃₁ (by simp <;> omega) (v := b.toData) (l₁ := [])
    (l₂ := (S v' ++ (ds X).l.drop v'.size).drop b.toData.size) (by simp <;> omega) (by simp <;> omega)
    (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₃₂
  obtain ⟨c₃₃, hr₃₃, hd₃₃⟩ := D_toEnd rfl (by decide) hd₃₂ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₃₃ hd₃₃
  have htail : (envRepr env'.tail).length ≤ (envRepr env').length := by
    cases env' <;> simp
  have hR := hr₁.trans hr₂
  have hR := hR.trans hr₃
  have hR := hR.trans hr₄
  have hR := hR.trans hr₅
  have hR := hR.trans hr₆
  have hR := hR.trans hr₇
  have hR := hR.trans hr₈
  have hR := hR.trans hr₉
  have hR := hR.trans hr₁₀
  have hR := hR.trans hr₁₁
  have hR := hR.trans hr₁₂
  have hR := hR.trans hr₁₃
  have hR := hR.trans hr₁₄
  have hR := hR.trans hr₁₅
  have hR := hR.trans hr₁₆
  have hR := hR.trans hr₁₇
  have hR := hR.trans hr₁₈
  have hR := hR.trans hr₁₉
  have hR := hR.trans hr₂₀
  have hR := hR.trans hr₂₁
  have hR := hR.trans hr₂₂
  have hR := hR.trans hr₂₃
  have hR := hR.trans hr₂₄
  have hR := hR.trans hr₂₅
  have hR := hR.trans hr₂₆
  have hR := hR.trans hr₂₇
  have hR := hR.trans hr₂₈
  have hR := hR.trans hr₂₉
  have hR := hR.trans hr₃₀
  have hR := hR.trans hr₃₁
  have hR := hR.trans hr₃₂
  have hR := hR.trans hr₃₃
  refine ⟨_, ?_, c₃₃, _, hR.cast_out (by simp), hd₃₃, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [caseBound, sz, ctrlRepr_ret, kontRepr_cons', frameBody_loop1, List.length_cons,
      List.length_append, length_S, List.length_singleton, List.length_nil, List.length_drop,
      Data.size_cons, Data.size_nil, S_cons, S_nil, envRepr_cons]
    omega
  · simp [ctrlRepr] <;> omega
  · simp [List.append_assoc] <;> omega
  · simp [kontRepr_cons, frameRepr, List.append_assoc] <;> omega
  · simp [hX]
  · simp [hX]
  · simp [hX]
  · try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret]
    simp only [sz, ctrlRepr_ret, kontRepr_cons', frameBody_loop1, List.length_cons, List.length_append,
      length_S, List.length_singleton, List.length_drop, List.length_nil, Data.size_cons, Data.size_nil,
      S_cons, S_nil]
    omega
end MIPRE.TM.Interp
