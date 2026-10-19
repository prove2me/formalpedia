-- Prove2me | solution 1 for MIPRE.TM.Interp.exec_checkLen
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:52:16.873994+00:00
-- url     : https://prove2.me/submissions/78b39990-fc5f-4d96-bcc3-4cd6c69b7391

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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/InputRoutines.lean (solution of MIPRE.TM.Interp.exec_checkLen);
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
import Definitions.Def_MIPRE_TM_Interp_InputRoutines

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
theorem cast_n {c c' : Cfg input} {n n' : ℕ} {out : List Sym} (h : Reach c n c' out)
    (e : n = n') : Reach c n' c' out := e ▸ h
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
theorem trans {c c' c'' : Cfg input} {SI SI' : List IT} {SW SW' : List WT}
    (h : Untouched c c' SI SW) (h' : Untouched c' c'' SI' SW') :
    Untouched c c'' (SI ++ SI') (SW ++ SW') := by
  refine ⟨fun j hj => ?_, fun d hd => ?_⟩
  · rw [List.mem_append, not_or] at hj
    exact (h'.1 j hj.2).trans (h.1 j hj.1)
  · rw [List.mem_append, not_or] at hd
    obtain ⟨h1, h2⟩ := h.2 d hd.1
    obtain ⟨h1', h2'⟩ := h'.2 d hd.2
    exact ⟨h1'.trans h1, h2'.trans h2⟩
end
end MIPRE.TM.Interp.Untouched

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
/-- The symbol under an input head at position `q + 1`, `q < |input j|`. -/
theorem inputSymbol_of_lt (c : Cfg input) (j : IT) {q : ℕ} (hq : (c.inputPos j : ℕ) = q + 1)
    (hlt : q < (input j).length) : c.inputSymbols j = some (input j)[q] :=
  inputSymbolInner j q (by omega) hlt
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem inputSymbol_end (c : Cfg input) (j : IT) (hq : (c.inputPos j : ℕ) = (input j).length + 1) :
    c.inputSymbols j = none := by
  simp only [Cfg.inputSymbols_apply, Cfg.inputSymbol]
  rw [dif_neg (by intro h; rw [h] at hq; simp at hq), dif_pos hq]
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
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem moveInputPos_val_one {n : ℕ} (p : Fin (n + 2)) (h : (p : ℕ) < n + 1) :
    (moveInputPos p 1 : ℕ) = p + 1 := moveInputPos_val_pos p h
end
end MIPRE.TM.Interp

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem _root_.solution {k : ProgId} {pc : Fin maxPc} {j ref : IT}
    (hins : instrAt k pc = .checkLen j ref) (hpc : pc.val + 1 < maxPc) (hjr : j ≠ ref) (m : ℕ) :
    ∀ (c : Cfg input) (q : ℕ), c.state = at_ k pc → (c.inputPos j : ℕ) = q + 1 →
      (c.inputPos ref : ℕ) = q + 1 → (input j).length = q + m → q + m ≤ (input ref).length →
    ∃ c', Reach c (m + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j, ref] [] ∧
      (c'.inputPos j : ℕ) = (input j).length + 1 ∧ (c'.inputPos ref : ℕ) = (input j).length + 1 := by
  induction m with
  | zero =>
    intro c q hq hpj hpr hlen _
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_end c j (by omega), Act.base_out, Option.toList_none,
      Act.base_next] at h
    refine ⟨_, h, by simp [resolve_adv k pc hpc], untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _,
      by simp; omega, by simp; omega⟩
  | succ m ih =>
    intro c q hq hpj hpr hlen hle
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_of_lt c j hpj (by omega), inputSymbol_of_lt c ref hpr (by omega),
      Act.mi_out, Act.base_out, Option.toList_none, Act.mi_next, Act.base_next, resolve_stay] at h
    set c₁ := applyAct (((Act.base (.stay p0)).mi j 1).mi ref 1) (some ⟨k, pc, p0⟩) c with hc₁
    have hu : Untouched c c₁ [j, ref] [] :=
      untouched_applyAct ⟨fun j' hj => by
        have h1 : j' ≠ j := fun e => hj (by simp [e])
        have h2 : j' ≠ ref := fun e => hj (by simp [e])
        simp [Act.mi, Function.update_of_ne h1, Function.update_of_ne h2], fun d _ => rfl⟩ _ _
    have hpj₁ : (c₁.inputPos j : ℕ) = (q + 1) + 1 := by
      simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_of_ne hjr,
        Function.update_self]
      rw [moveInputPos_val_one (c.inputPos j) (by omega), hpj]
    have hpr₁ : (c₁.inputPos ref : ℕ) = (q + 1) + 1 := by
      simp only [hc₁, applyAct_inputPos, Act.mi_inMoves, Function.update_self]
      rw [moveInputPos_val_one (c.inputPos ref) (by omega), hpr]
    obtain ⟨c', hr, hst, hu', hpj', hpr'⟩ := ih c₁ (q + 1) (by simp [hc₁]) hpj₁ hpr₁ (by omega) (by omega)
    exact ⟨c', ((h.trans hr).cast_n (by omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), hpj', hpr'⟩
end MIPRE.TM.Interp
