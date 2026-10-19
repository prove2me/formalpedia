-- Prove2me | solution 1 for MIPRE.TM.Interp.init_run
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:55:57.995298+00:00
-- url     : https://prove2.me/submissions/ceaee439-e2d8-4fb2-85bf-d17793345dee

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

/-
Vendored from CSLib (https://github.com/leanprover/cslib), upstream file
  Cslib/Computability/Machines/Turing/MultiTape/Deterministic.lean
at commit 3aa9d4416c185e0b9faeb72bbd65abe85b95dbcc (2026-08-03); fetched 2026-08-05.

CSLib cannot currently be a Lake dependency of this project: its MultiTape development
requires Lean >= v4.33.0-rc1, while this project pins v4.32.0. See
`planning/tm-infrastructure.md` (decision D1). Delete this copy and `require` CSLib once
the toolchains align.

Adaptations (the only differences from upstream):
* module-system markers removed: the `module` line, `public import` -> `import`, and the
  `@[expose] public section` line (replaced by the `set_option` lines below);
* `set_option autoImplicit true` / `set_option relaxedAutoImplicit true` added to restore
  the upstream Lean defaults (this project's lakefile disables both);
* the `RelatesInSteps` import redirected to the vendored copy (`MIPRE.Cslib...`);
* `open Cslib Relation` -> `open Relation` (the `Cslib` namespace is not vendored).
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Run.lean (solution of MIPRE.TM.Interp.init_run);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
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
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Theorems.Thm_MIPRE_TM_Interp_TapeIs_of_overwrite
import Theorems.Thm_MIPRE_TM_Interp_exec_buildAnswer
import Theorems.Thm_MIPRE_TM_Interp_exec_checkLen
import Theorems.Thm_MIPRE_TM_Interp_exec_copyInputBits
import Theorems.Thm_MIPRE_TM_Interp_exec_copyUnary
import Theorems.Thm_MIPRE_TM_Interp_exec_rewindInput

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace Turing.MultiTapeTM
section
open Relation
set_option autoImplicit true
set_option relaxedAutoImplicit true
variable {k : ℕ} {State Symbol : Type*}
variable {tm : MultiTapeTM k Symbol State}
/-- A right move away from the right input boundary increments the native input position. -/
lemma moveInputPos_pos_of_ne_right {n : ℕ} (p : Fin (n + 2)) (h : p.val ≠ n + 1) :
    moveInputPos p .pos = ⟨p.val + 1, by have := p.isLt; omega⟩ := by
  unfold moveInputPos
  rw [dif_pos]
  · apply Fin.ext
    simp
  · simp
    omega
end
end Turing.MultiTapeTM

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

namespace MIPRE.TM.Interp.Holds
section
variable {τ : Tape} {p : ℤ}
theorem cons_iff {s : Sym} {l : List Sym} :
    Holds τ p (s :: l) ↔ τ p = some s ∧ Holds τ (p + 1) l := by
  constructor
  · intro h
    refine ⟨?_, fun k hk => ?_⟩
    · have h0 := h 0 (by simp)
      rw [Nat.cast_zero, add_zero] at h0
      exact h0
    · have := h (k + 1) (by simp; omega)
      rw [List.getElem_cons_succ] at this
      convert this using 2
      push_cast; ring
  · rintro ⟨h0, h⟩ k hk
    cases k with
    | zero => rw [Nat.cast_zero, add_zero]; exact h0
    | succ k =>
      have := h k (by simpa using hk)
      rw [List.getElem_cons_succ]
      convert this using 2
      push_cast; ring
end
end MIPRE.TM.Interp.Holds

namespace MIPRE.TM.Interp.Holds
section
variable {τ : Tape} {p : ℤ}
theorem singleton_iff {s : Sym} : Holds τ p [s] ↔ τ p = some s := by
  simp [cons_iff]
end
end MIPRE.TM.Interp.Holds

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

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
variable (a : Act) (q' : Option Ctl) (c : Cfg input)
theorem applyAct_workTapes_of_some (d : WT) {s : Option Sym} (h : (a.works d).1 = some s) :
    (applyAct a q' c).workTapes d = Function.update (c.workTapes d) (c.workTapePos d) s := by
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

namespace MIPRE.TM.Interp.Act
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem ww_works_of_ne (a : Act) {t t' : WT} (h : t' ≠ t) (s : Option Sym) :
    (a.ww t s).works t' = a.works t' := by simp [ww, Function.update_of_ne h]
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

namespace MIPRE.TM.Interp.Untouched
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem inputPos {c c' : Cfg input} {SI : List IT} {SW : List WT} (h : Untouched c c' SI SW) {j : IT}
    (hj : j ∉ SI) : c'.inputPos j = c.inputPos j := h.1 j hj
end
end MIPRE.TM.Interp.Untouched

namespace MIPRE.TM.Interp.Untouched
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem inputPos_eq {c c' : Cfg input} {SW : List WT} (h : Untouched c c' [] SW) :
    c'.inputPos = c.inputPos := funext fun j => h.1 j (by simp)
end
end MIPRE.TM.Interp.Untouched

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
theorem exec_write {k : ProgId} {pc : Fin maxPc} {t : WT} {s : Sym}
    (hins : instrAt k pc = .write t s) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some s) ∧
      c'.workTapePos t = c.workTapePos t + 1 := by
  have h := step_instr hq hins
  simp only [execInstr] at h
  refine ⟨_, h, ?_, ?_, ?_, ?_⟩
  · simp [resolve_adv k pc hpc]
  · refine untouched_applyAct ⟨fun j _ => rfl, fun d hd => ?_⟩ _ _
    have : d ≠ t := by simpa using hd
    simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]
  · rw [applyAct_workTapes_of_some _ _ _ t (s := some s) (by simp)]
  · simp
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
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem moveInputPos_val_pos {n : ℕ} (p : Fin (n + 2)) (h : (p : ℕ) < n + 1) :
    (moveInputPos p .pos : ℕ) = p + 1 := by
  rw [MultiTapeTM.moveInputPos_pos_of_ne_right p (by omega)]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem exec_moveInput {k : ProgId} {pc : Fin maxPc} {j : IT} {dir : Bool}
    (hins : instrAt k pc = .moveInput j dir) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j] [] ∧
      c'.inputPos j = moveInputPos (c.inputPos j) (if dir then 1 else -1) := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mi_out, Act.base_out, Option.toList_none, Act.mi_next, Act.base_next] at h
  refine ⟨_, h, by simp [resolve_adv k pc hpc], ?_, ?_⟩
  · exact untouched_applyAct ⟨fun j' hj => by
      have : j' ≠ j := by simpa using hj
      simp [Act.mi, Function.update_of_ne this], fun d _ => rfl⟩ _ _
  · cases dir <;> simp [Act.mi]
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
theorem pos_eq (h : TapeIs τ pos s) : pos = s.p := h.2.2.2
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
theorem D_jump {target : ProgId} (hins : instrAt k pc = .jump target) (hd : Desc c (at_ k pc) ds) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (at_ target ⟨0, by decide⟩) ds := by
  obtain ⟨c', hr, hst, hu, hall⟩ := exec_jump hins c hd.state
  exact ⟨c', hr, hd.of_untouched (SW := []) (hu.mono (by simp) (by simp)) hst (by simp)
    (fun _ _ => rfl)⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem moveInputPos_val_one {n : ℕ} (p : Fin (n + 2)) (h : (p : ℕ) < n + 1) :
    (moveInputPos p 1 : ℕ) = p + 1 := moveInputPos_val_pos p h
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
theorem mem_bits (l : List Bool) : ∀ s ∈ bits l, s = .zero ∨ s = .one := by
  intro s hs
  simp only [bits, List.mem_map] at hs
  obtain ⟨b, -, rfl⟩ := hs
  cases b <;> simp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
theorem map_boolOf_bits (l : List Bool) : (bits l).map boolOf = l := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [bits, boolOf] at ih ⊢ <;> exact ih
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
theorem answerBits_bits (l : BitStr) : answerBits (bits l) = S (encode l) := by
  simp [answerBits, map_boolOf_bits]; rfl
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
theorem encode_prod {α β : Type*} [SizedEncoding α] [SizedEncoding β] (p : α × β) :
    encode p = .cons (encode p.1) (encode p.2) := rfl
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem InPos.of_untouched {c c' : Cfg input} {f : IT → ℕ} (h : InPos c f) {SW : List WT}
    (hu : Untouched c c' [] SW) : InPos c' f := by
  intro j; rw [hu.inputPos_eq]; exact h j
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
/-- A run touching only input heads leaves the descriptions. -/
theorem Desc.of_untouched_inputs {c c' : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}
    (hd : Desc c q ds) {SI : List IT} (hu : Untouched c c' SI []) {q' : Option Ctl}
    (hs : c'.state = q') : Desc c' q' ds :=
  ⟨hs, fun t => by rw [hu.tapes (d := t) (by simp), hu.pos (d := t) (by simp)]; exact hd.tape t⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem InPos.update {c c' : Cfg input} {f : IT → ℕ} (h : InPos c f) {j : IT} {SW : List WT}
    (hu : Untouched c c' [j] SW) {v : ℕ} (hv : (c'.inputPos j : ℕ) = v) :
    InPos c' (Function.update f j v) := by
  intro j'
  by_cases hj : j' = j
  · subst hj; simpa using hv
  · rw [Function.update_of_ne hj, hu.inputPos (by simpa using hj)]; exact h j'
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem InPos.update₂ {c c' : Cfg input} {f : IT → ℕ} (h : InPos c f) {j j' : IT} {SW : List WT}
    (hu : Untouched c c' [j, j'] SW) {v v' : ℕ} (hv : (c'.inputPos j : ℕ) = v)
    (hv' : (c'.inputPos j' : ℕ) = v') (hjj : j ≠ j') :
    InPos c' (Function.update (Function.update f j v) j' v') := by
  intro i
  by_cases hi' : i = j'
  · subst hi'; simpa using hv'
  by_cases hi : i = j
  · subst hi; rw [Function.update_of_ne hjj, Function.update_self]; exact hv
  · rw [Function.update_of_ne hi', Function.update_of_ne hi, hu.inputPos (by simp [hi, hi'])]
    exact h i
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}
theorem I_jump {target : ProgId} (hins : instrAt k pc = .jump target) (hd : Desc c (at_ k pc) ds)
    (hi : InPos c f) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (at_ target ⟨0, by decide⟩) ds ∧ InPos c' f := by
  obtain ⟨c', hr, hs, hu, _⟩ := exec_jump hins c hd.state
  obtain ⟨c'', hr', hd'⟩ := D_jump hins hd
  have e : c'' = c' := by rw [← hr.1, ← hr'.1]
  subst e
  exact ⟨c'', hr', hd', hi.of_untouched hu⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}
/-- A written effect on `dst` at the end of its content, as a description. -/
theorem Desc.of_weff_end {q : Option Ctl} (hd : Desc c q ds) {c' : Cfg input} {dst : WT}
    {SI : List IT} (hu : Untouched c c' SI [dst]) {q' : Option Ctl} (hs : c'.state = q')
    {w : List Sym} (hw : WEff dst c c' w) (hp : (ds dst).p = (ds dst).l.length) :
    Desc c' q' (Function.update ds dst ⟨(ds dst).l ++ w, ((ds dst).l ++ w).length⟩) := by
  refine ⟨hs, fun t => ?_⟩
  by_cases ht : t = dst
  · subst ht
    rw [Function.update_self]
    have := (hd.tape t).of_overwrite (p' := ((ds t).l ++ w).length) (pos' := c'.workTapePos t)
      hp.le (by rw [← hd.pos]; exact hw.holds) (fun q hq => hw.outside q (by rw [hd.pos]; exact hq))
      (by rw [hw.pos, hd.pos, hp]; simp)
    rwa [overwrite_append_nil _ _ hp] at this
  · rw [Function.update_of_ne ht, hu.tapes (d := t) (by simpa using ht), hu.pos (d := t) (by simpa using ht)]
    exact hd.tape t
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}
theorem I_write_end {t : WT} {s : Sym} (hins : instrAt k pc = .write t s) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : (ds t).p = (ds t).l.length) (hi : InPos c f) :
    ∃ c', Reach c 1 c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l ++ [s], ((ds t).l ++ [s]).length⟩) ∧
      InPos c' f := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_write hins hpc c hd.state
  refine ⟨c', hr, hd.of_weff_end (SI := []) hu hs ⟨?_, ?_, ?_⟩ hp, hi.of_untouched hu⟩
  · rw [Holds.singleton_iff, htape, Function.update_self]
  · intro q hq
    rw [htape, Function.update_of_ne (by simp only [List.length_singleton] at hq; omega)]
  · rw [hpos]; simp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}
theorem I_copyUnary_end {j : IT} {dst : WT} (hins : instrAt k pc = .copyUnary j dst)
    (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds) (hi : InPos c f) (hj : f j = 1)
    (hp : (ds dst).p = (ds dst).l.length) :
    ∃ c', Reach c ((input j).length + 1) c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds dst
        ⟨(ds dst).l ++ List.replicate (input j).length Sym.one,
          ((ds dst).l ++ List.replicate (input j).length Sym.one).length⟩) ∧
      InPos c' (Function.update f j ((input j).length + 1)) := by
  obtain ⟨c', hr, hs, hu, hj', hw⟩ := exec_copyUnary hins hpc (input j).length c 0 hd.state
    (by rw [hi j, hj]) (by simp)
  exact ⟨c', hr, hd.of_weff_end hu hs hw hp, hi.update hu hj'⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}
theorem I_copyInputBits_end {j : IT} {dst : WT} (hins : instrAt k pc = .copyInputBits j dst)
    (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds) (hi : InPos c f) (hj : f j = 1)
    (hp : (ds dst).p = (ds dst).l.length) :
    ∃ c', Reach c ((input j).length + 1) c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds dst
        ⟨(ds dst).l ++ input j, ((ds dst).l ++ input j).length⟩) ∧
      InPos c' (Function.update f j ((input j).length + 1)) := by
  obtain ⟨c', hr, hs, hu, hj', hw⟩ := exec_copyInputBits hins hpc (input j).length c 0 hd.state
    (by rw [hi j, hj]) (by simp)
  simp only [List.drop_zero] at hw
  exact ⟨c', hr, hd.of_weff_end hu hs hw hp, hi.update hu hj'⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}
theorem I_buildAnswer_end {j : IT} {dst : WT} (hins : instrAt k pc = .buildAnswer j dst)
    (hpc : pc.val + 1 < maxPc) (hbits : ∀ s ∈ input j, s = .zero ∨ s = .one)
    (hd : Desc c (at_ k pc) ds) (hi : InPos c f) (hj : f j = 1)
    (hp : (ds dst).p = (ds dst).l.length) :
    ∃ n ≤ 4 * (input j).length + 1, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds dst
        ⟨(ds dst).l ++ answerBits (input j), ((ds dst).l ++ answerBits (input j)).length⟩) ∧
      InPos c' (Function.update f j ((input j).length + 1)) := by
  obtain ⟨n, hn, c', hr, hs, hu, hj', hw⟩ := exec_buildAnswer hins hpc hbits (input j).length c 0
    hd.state (by rw [hi j, hj]) (by simp)
  simp only [List.drop_zero] at hw
  exact ⟨n, hn, c', hr, hd.of_weff_end hu hs hw hp, hi.update hu hj'⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}
theorem I_checkLen {j ref : IT} (hins : instrAt k pc = .checkLen j ref) (hpc : pc.val + 1 < maxPc)
    (hjr : j ≠ ref) (hd : Desc c (at_ k pc) ds) (hi : InPos c f) (hj : f j = 1) (hr : f ref = 1)
    (hlen : (input j).length ≤ (input ref).length) :
    ∃ c', Reach c ((input j).length + 1) c' [] ∧ Desc c' (next_ k pc hpc) ds ∧
      InPos c' (Function.update (Function.update f j ((input j).length + 1)) ref
        ((input j).length + 1)) := by
  obtain ⟨c', hr', hs, hu, hj', hr''⟩ := exec_checkLen hins hpc hjr (input j).length c 0 hd.state
    (by rw [hi j, hj]) (by rw [hi ref, hr]) (by simp) (by simpa using hlen)
  exact ⟨c', hr', hd.of_untouched_inputs hu hs, hi.update₂ hu hj' hr'' hjr⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}
theorem I_rewindInput {j : IT} (hins : instrAt k pc = .rewindInput j) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hi : InPos c f) :
    ∃ n ≤ f j + 2, ∃ c', Reach c n c' [] ∧ Desc c' (next_ k pc hpc) ds ∧
      InPos c' (Function.update f j 0) := by
  obtain ⟨n, hn, c', hr, hs, hu, hj'⟩ := exec_rewindInput hins hpc c hd.state
  exact ⟨n, by rw [hi j] at hn; exact hn, c', hr, hd.of_untouched_inputs hu hs, hi.update hu hj'⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt} {f : IT → ℕ}
theorem I_moveInput_right {j : IT} (hins : instrAt k pc = .moveInput j true)
    (hpc : pc.val + 1 < maxPc) (hd : Desc c (at_ k pc) ds) (hi : InPos c f)
    (hlt : f j < (input j).length + 1) :
    ∃ c', Reach c 1 c' [] ∧ Desc c' (next_ k pc hpc) ds ∧ InPos c' (Function.update f j (f j + 1)) := by
  obtain ⟨c', hr, hs, hu, hj'⟩ := exec_moveInput hins hpc c hd.state
  refine ⟨c', hr, hd.of_untouched_inputs hu hs, hi.update hu ?_⟩
  rw [hj', if_pos rfl, moveInputPos_val_one _ (by rw [hi j]; exact hlt), hi j]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
/-- The initial configuration is described by empty tapes. -/
theorem desc_initCfg (input : Fin 7 → List Sym) :
    Desc (U.initCfg input) (at_ .init 0) (fun _ => ⟨[], 0⟩) := by
  refine ⟨rfl, fun t => ⟨Holds.nil, fun _ _ => rfl, fun _ _ => rfl, rfl⟩⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem inPos_initCfg (input : Fin 7 → List Sym) : InPos (U.initCfg input) (fun _ => 1) :=
  fun j => by simp [initCfg]
end
end MIPRE.TM.Interp

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem _root_.solution (D : Prog) (n : ℕ) (x y a b : BitStr) (Tb : ℕ) (ha : a.length ≤ Tb)
    (hb : b.length ≤ Tb) :
    ∃ m ≤ initBound D n x y a b Tb, ∃ (c : Cfg (uInput D n Tb x y a b)) (ds : WT → TapeSt),
      Reach (U.initCfg (uInput D n Tb x y a b)) m c [] ∧ Desc c (at_ .dispatch 0) ds ∧
      RepOf ds ⟨.ev D, [encode (n, x, y, a, b)], []⟩ Tb (ctrlRepr (.ev D)).length 0 ∧
      (ds X).l.length = 0 := by
  have hd := desc_initCfg (uInput D n Tb x y a b)
  have hi := inPos_initCfg (uInput D n Tb x y a b)
  obtain ⟨c₁, hr₁, hd₁, hi₁⟩ := I_copyUnary_end rfl (by decide) hd hi rfl rfl
  simp only [uInput_T, List.length_replicate] at hr₁ hd₁ hi₁
  obtain ⟨n₂, hn₂, c₂, hr₂, hd₂, hi₂⟩ := I_rewindInput rfl (by decide) hd₁ hi₁
  simp at hn₂
  obtain ⟨c₃, hr₃, hd₃, hi₃⟩ := I_moveInput_right rfl (by decide) hd₂ hi₂ (by simp)
  obtain ⟨c₄, hr₄, hd₄, hi₄⟩ := I_checkLen rfl (by decide) (by decide) hd₃ hi₃ (by simp) (by simp)
    (by simpa using ha)
  simp only [uInput_A, length_bits] at hr₄ hi₄
  obtain ⟨n₅, hn₅, c₅, hr₅, hd₅, hi₅⟩ := I_rewindInput rfl (by decide) hd₄ hi₄
  simp at hn₅
  obtain ⟨c₆, hr₆, hd₆, hi₆⟩ := I_moveInput_right rfl (by decide) hd₅ hi₅ (by simp)
  obtain ⟨n₇, hn₇, c₇, hr₇, hd₇, hi₇⟩ := I_rewindInput rfl (by decide) hd₆ hi₆
  simp at hn₇
  obtain ⟨c₈, hr₈, hd₈, hi₈⟩ := I_moveInput_right rfl (by decide) hd₇ hi₇ (by simp)
  obtain ⟨c₉, hr₉, hd₉, hi₉⟩ := I_checkLen rfl (by decide) (by decide) hd₈ hi₈ (by simp) (by simp)
    (by simpa using hb)
  simp only [uInput_B, length_bits] at hr₉ hi₉
  obtain ⟨n₁₀, hn₁₀, c₁₀, hr₁₀, hd₁₀, hi₁₀⟩ := I_rewindInput rfl (by decide) hd₉ hi₉
  simp at hn₁₀
  obtain ⟨c₁₁, hr₁₁, hd₁₁, hi₁₁⟩ := I_moveInput_right rfl (by decide) hd₁₀ hi₁₀ (by simp)
  obtain ⟨c₁₂, hr₁₂, hd₁₂, hi₁₂⟩ := I_write_end rfl (by decide) hd₁₁ (by simp) hi₁₁
  obtain ⟨c₁₃, hr₁₃, hd₁₃, hi₁₃⟩ := I_copyInputBits_end rfl (by decide) hd₁₂ hi₁₂ (by simp) (by simp)
  simp only [uInput_PROG] at hr₁₃ hd₁₃ hi₁₃
  obtain ⟨c₁₄, hr₁₄, hd₁₄, hi₁₄⟩ := I_write_end rfl (by decide) hd₁₃ (by simp) hi₁₃
  obtain ⟨c₁₅, hr₁₅, hd₁₅, hi₁₅⟩ := I_copyInputBits_end rfl (by decide) hd₁₄ hi₁₄ (by simp) (by simp)
  simp only [uInput_N] at hr₁₅ hd₁₅ hi₁₅
  obtain ⟨c₁₆, hr₁₆, hd₁₆, hi₁₆⟩ := I_write_end rfl (by decide) hd₁₅ (by simp) hi₁₅
  obtain ⟨c₁₇, hr₁₇, hd₁₇, hi₁₇⟩ := I_copyInputBits_end rfl (by decide) hd₁₆ hi₁₆ (by simp) (by simp)
  simp only [uInput_XS] at hr₁₇ hd₁₇ hi₁₇
  obtain ⟨c₁₈, hr₁₈, hd₁₈, hi₁₈⟩ := I_write_end rfl (by decide) hd₁₇ (by simp) hi₁₇
  obtain ⟨c₁₉, hr₁₉, hd₁₉, hi₁₉⟩ := I_copyInputBits_end rfl (by decide) hd₁₈ hi₁₈ (by simp) (by simp)
  simp only [uInput_YS] at hr₁₉ hd₁₉ hi₁₉
  obtain ⟨c₂₀, hr₂₀, hd₂₀, hi₂₀⟩ := I_write_end rfl (by decide) hd₁₉ (by simp) hi₁₉
  obtain ⟨n₂₁, hn₂₁, c₂₁, hr₂₁, hd₂₁, hi₂₁⟩ := I_buildAnswer_end rfl (by decide) (mem_bits a) hd₂₀
    hi₂₀ (by simp) (by simp)
  simp only [uInput_A, length_bits, answerBits_bits] at hn₂₁ hd₂₁ hi₂₁
  obtain ⟨n₂₂, hn₂₂, c₂₂, hr₂₂, hd₂₂, hi₂₂⟩ := I_buildAnswer_end rfl (by decide) (mem_bits b) hd₂₁
    hi₂₁ (by simp) (by simp)
  simp only [uInput_B, length_bits, answerBits_bits] at hn₂₂ hd₂₂ hi₂₂
  obtain ⟨c₂₃, hr₂₃, hd₂₃, hi₂₃⟩ := I_write_end rfl (by decide) hd₂₂ (by simp) hi₂₂
  obtain ⟨c₂₄, hr₂₄, hd₂₄, hi₂₄⟩ := I_jump rfl hd₂₃ hi₂₃
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
  refine ⟨_, ?_, c₂₄, _, hR.cast_out (by simp), hd₂₄, ⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [initBound]; omega
  · exact ⟨[], by simp [ctrlRepr]⟩
  · simp [encode_prod, S_cons, List.append_assoc]
  · simp
  · simp
  · simp
  · simp
  · simp
end MIPRE.TM.Interp
