-- Prove2me | solution 1 for MIPRE.TM.Interp.exec_buildAnswer
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:52:18.869173+00:00
-- url     : https://prove2.me/submissions/955d58f3-4b31-4500-be38-0232d0850a5a

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
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/InputRoutines.lean (solution of MIPRE.TM.Interp.exec_buildAnswer);
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
theorem append_iff {l₁ l₂ : List Sym} :
    Holds τ p (l₁ ++ l₂) ↔ Holds τ p l₁ ∧ Holds τ (p + l₁.length) l₂ := by
  induction l₁ generalizing p with
  | nil => simp
  | cons s l ih =>
    have e : p + ((l.length + 1 : ℕ) : ℤ) = p + 1 + (l.length : ℤ) := by push_cast; ring
    simp only [List.cons_append, cons_iff, ih, List.length_cons, e]
    tauto
end
end MIPRE.TM.Interp.Holds

namespace MIPRE.TM.Interp.Holds
section
variable {τ : Tape} {p : ℤ}
theorem append {l₁ l₂ : List Sym} (h₁ : Holds τ p l₁) (h₂ : Holds τ (p + l₁.length) l₂) :
    Holds τ p (l₁ ++ l₂) := append_iff.mpr ⟨h₁, h₂⟩
end
end MIPRE.TM.Interp.Holds

namespace MIPRE.TM.Interp.Holds
section
variable {τ : Tape} {p : ℤ}
/-- Two tapes agreeing on the held region hold the same. -/
theorem congr {τ' : Tape} {l : List Sym} (h : Holds τ p l)
    (hagree : ∀ q, p ≤ q → q < p + l.length → τ' q = τ q) : Holds τ' p l := by
  intro k hk
  rw [hagree _ (by omega) (by omega)]
  exact h k hk
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
/-- Writing a symbol at the head, then holding it: `Holds (update τ p (some s)) p [s]`. -/
theorem holds_update_self (τ : Tape) (p : ℤ) (s : Sym) :
    Holds (Function.update τ p (some s)) p [s] := by
  rw [Holds.singleton_iff, Function.update_self]
end
end MIPRE.TM.Interp

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
open MIPRE.Cost MIPRE.Cost.Machine
theorem S_cons (a b : Data) : S (.cons a b) = .one :: (S a ++ S b) := by
  simp [S, Data.toBits]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem WEff.trans {t : WT} {c c' c'' : Cfg input} {l l' : List Sym} (h : WEff t c c' l)
    (h' : WEff t c' c'' l') : WEff t c c'' (l ++ l') where
  holds := by
    refine Holds.append ?_ ?_
    · exact h.holds.congr fun q hq1 hq2 => h'.outside q (Or.inl (by rw [h.pos]; omega))
    · rw [← h.pos]; exact h'.holds
  outside q hq := by
    simp only [List.length_append, Nat.cast_add] at hq
    rw [h'.outside q (by rw [h.pos]; omega), h.outside q (by omega)]
  pos := by rw [h'.pos, h.pos, List.length_append]; push_cast; ring
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem WEff.cast {t : WT} {c c' : Cfg input} {l l' : List Sym} (h : WEff t c c' l)
    (e : l = l') : WEff t c c' l' := e ▸ h
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
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem WEff.single {t : WT} {c c' : Cfg input} {s : Sym}
    (htape : c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some s))
    (hpos : c'.workTapePos t = c.workTapePos t + 1) : WEff t c c' [s] where
  holds := by rw [htape]; exact holds_update_self _ _ _
  outside q hq := by
    rw [htape, Function.update_of_ne]
    simp only [List.length_singleton, Nat.cast_one] at hq
    omega
  pos := by simp [hpos]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem answerBits_nil : answerBits [] = [.zero] := rfl
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem answerBits_zero (l : List Sym) : answerBits (.zero :: l) = .one :: .zero :: answerBits l := by
  simp [answerBits, Data.ofList, boolOf, Data.ofBool, S_cons]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem answerBits_one (l : List Sym) :
    answerBits (.one :: l) = .one :: .one :: .zero :: .zero :: answerBits l := by
  simp [answerBits, Data.ofList, boolOf, Data.ofBool, S_cons]
end
end MIPRE.TM.Interp

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem _root_.solution {k : ProgId} {pc : Fin maxPc} {j : IT} {dst : WT}
    (hins : instrAt k pc = .buildAnswer j dst) (hpc : pc.val + 1 < maxPc)
    (hbits : ∀ s ∈ input j, s = .zero ∨ s = .one) (m : ℕ) :
    ∀ (c : Cfg input) (q : ℕ), c.state = at_ k pc → (c.inputPos j : ℕ) = q + 1 →
      (input j).length = q + m →
    ∃ n ≤ 4 * m + 1, ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [j] [dst] ∧
      (c'.inputPos j : ℕ) = (input j).length + 1 ∧ WEff dst c c' (answerBits ((input j).drop q)) := by
  induction m with
  | zero =>
    intro c q hq hpos hlen
    have h := step_instr hq hins
    simp only [execInstr, inputSymbol_end c j (by omega), Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next] at h
    refine ⟨1, by omega, _, h, by simp [resolve_adv k pc hpc], ?_, by simp; omega, ?_⟩
    · exact untouched_applyAct ⟨fun _ _ => rfl, fun d hd => by
        have : d ≠ dst := by simpa using hd
        simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
    · rw [List.drop_of_length_le (by omega), answerBits_nil]
      exact WEff.single (by rw [applyAct_workTapes_of_some _ _ _ dst (s := some .zero) (by simp)])
        (by simp)
  | succ m ih =>
    intro c q hq hpos hlen
    have hmem : (input j)[q] ∈ input j := List.getElem_mem (by omega)
    -- a helper: a write step at phase `ph` moving to phase `ph'`, with or without an input move
    have wstep : ∀ (c₀ : Cfg input) (ph ph' : Phase) (s : Sym) (mv : Bool),
        c₀.state = some ⟨k, pc, ph⟩ →
        execInstr (.buildAnswer j dst) ph c₀.inputSymbols c₀.workTapeSymbols =
          (if mv then (((Act.base (.stay ph')).ww dst (some s)).mw dst 1).mi j 1
            else ((Act.base (.stay ph')).ww dst (some s)).mw dst 1) →
        ∃ c₁, Reach c₀ 1 c₁ [] ∧ c₁.state = some ⟨k, pc, ph'⟩ ∧ Untouched c₀ c₁ [j] [dst] ∧
          WEff dst c₀ c₁ [s] ∧
          c₁.inputPos j = moveInputPos (c₀.inputPos j) (if mv then 1 else 0) := by
      intro c₀ ph ph' s mv hq₀ hact
      have h := step_instr hq₀ hins
      rw [hact] at h
      cases mv
      · simp only [if_false, Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none,
          Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h
        refine ⟨_, h, rfl, ?_, WEff.single ?_ (by simp), ?_⟩
        · exact untouched_applyAct ⟨fun _ _ => rfl, fun d hd => by
            have : d ≠ dst := by simpa using hd
            simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
        · rw [applyAct_workTapes_of_some _ _ _ dst (s := some s) (by simp)]
        · simp
      · simp only [if_true, Act.mi_out, Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none,
          Act.mi_next, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h
        refine ⟨_, h, rfl, ?_, WEff.single ?_ (by simp), ?_⟩
        · exact untouched_applyAct ⟨fun j' hj => by
            have : j' ≠ j := by simpa using hj
            simp [Act.mi, Function.update_of_ne this], fun d hd => by
            have : d ≠ dst := by simpa using hd
            simp [Act.mw_works_of_ne _ this, Act.ww_works_of_ne _ this]⟩ _ _
        · rw [applyAct_workTapes_of_some _ _ _ dst (s := some s) (by simp)]
        · simp [Act.mi]
    rcases hbits _ hmem with h0 | h1
    · -- a `0`: write `1 0`
      obtain ⟨c₁, hr₁, hs₁, hu₁, hw₁, hp₁⟩ := wstep c p0 p1 .one false hq (by
        simp only [execInstr, inputSymbol_of_lt c j hpos (by omega), h0]; rfl)
      have hpos₁ : (c₁.inputPos j : ℕ) = q + 1 := by rw [hp₁]; simp [hpos]
      obtain ⟨c₂, hr₂, hs₂, hu₂, hw₂, hp₂⟩ := wstep c₁ p1 p0 .zero true hs₁ (by
        simp only [execInstr]; rfl)
      have hpos₂ : (c₂.inputPos j : ℕ) = (q + 1) + 1 := by
        rw [hp₂]; simp only [if_true]; rw [moveInputPos_val_one (c₁.inputPos j) (by omega), hpos₁]
      obtain ⟨n, hn, c', hr, hst, hu', hpos', hw'⟩ := ih c₂ (q + 1) hs₂ hpos₂ (by omega)
      refine ⟨n + 2, by omega, c', ?_, hst, ?_, hpos', ?_⟩
      · exact (((hr₁.trans hr₂).trans hr).cast_n (by omega)).cast_out (by simp)
      · exact ((hu₁.trans hu₂).trans hu').mono (by simp) (by simp)
      · rw [List.drop_eq_getElem_cons (by omega), h0, answerBits_zero]
        exact ((hw₁.trans hw₂).trans hw').cast (by simp)
    · -- a `1`: write `1 1 0 0`
      obtain ⟨c₁, hr₁, hs₁, hu₁, hw₁, hp₁⟩ := wstep c p0 p2 .one false hq (by
        simp only [execInstr, inputSymbol_of_lt c j hpos (by omega), h1]; rfl)
      have hpos₁ : (c₁.inputPos j : ℕ) = q + 1 := by rw [hp₁]; simp [hpos]
      obtain ⟨c₂, hr₂, hs₂, hu₂, hw₂, hp₂⟩ := wstep c₁ p2 p3 .one false hs₁ (by
        simp only [execInstr]; rfl)
      have hpos₂ : (c₂.inputPos j : ℕ) = q + 1 := by rw [hp₂]; simp [hpos₁]
      obtain ⟨c₃, hr₃, hs₃, hu₃, hw₃, hp₃⟩ := wstep c₂ p3 p4 .zero false hs₂ (by
        simp only [execInstr]; rfl)
      have hpos₃ : (c₃.inputPos j : ℕ) = q + 1 := by rw [hp₃]; simp [hpos₂]
      obtain ⟨c₄, hr₄, hs₄, hu₄, hw₄, hp₄⟩ := wstep c₃ p4 p0 .zero true hs₃ (by
        simp only [execInstr]; rfl)
      have hpos₄ : (c₄.inputPos j : ℕ) = (q + 1) + 1 := by
        rw [hp₄]; simp only [if_true]; rw [moveInputPos_val_one (c₃.inputPos j) (by omega), hpos₃]
      obtain ⟨n, hn, c', hr, hst, hu', hpos', hw'⟩ := ih c₄ (q + 1) hs₄ hpos₄ (by omega)
      refine ⟨n + 4, by omega, c', ?_, hst, ?_, hpos', ?_⟩
      · exact (((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr).cast_n (by omega)).cast_out
          (by simp)
      · exact ((((hu₁.trans hu₂).trans hu₃).trans hu₄).trans hu').mono (by simp) (by simp)
      · rw [List.drop_eq_getElem_cons (by omega), h1, answerBits_one]
        exact ((((hw₁.trans hw₂).trans hw₃).trans hw₄).trans hw').cast (by simp)
end MIPRE.TM.Interp
