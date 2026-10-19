-- Prove2me | solution 1 for MIPRE.TM.Interp.step_fail
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:08:03.607238+00:00
-- url     : https://prove2.me/submissions/d699e2fb-962f-4eb0-bbe0-dc79d488cec6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Step.lean (solution of MIPRE.TM.Interp.step_fail);
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
import Theorems.Thm_MIPRE_TM_Interp_D_copyTree_charge
import Theorems.Thm_MIPRE_TM_Interp_D_getEnv
import Theorems.Thm_MIPRE_TM_Interp_D_rewind
import Theorems.Thm_MIPRE_TM_Interp_D_write
import Theorems.Thm_MIPRE_TM_Interp_case_evCons
import Theorems.Thm_MIPRE_TM_Interp_case_evElim_cons
import Theorems.Thm_MIPRE_TM_Interp_case_evElim_nil
import Theorems.Thm_MIPRE_TM_Interp_case_evLet
import Theorems.Thm_MIPRE_TM_Interp_case_retLoopCont
import Theorems.Thm_MIPRE_TM_Interp_case_retLoopNil
import Theorems.Thm_MIPRE_TM_Interp_case_retLoopStop
import Theorems.Thm_MIPRE_TM_Interp_copyTree_scan_fail
import Theorems.Thm_MIPRE_TM_Interp_dispatch_ev
import Theorems.Thm_MIPRE_TM_Interp_dispatch_ret
import Theorems.Thm_MIPRE_TM_Interp_exec_charge_one_fail
import Theorems.Thm_MIPRE_TM_Interp_size_get_le

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
theorem of_append_left {l₁ l₂ : List Sym} (h : Holds τ p (l₁ ++ l₂)) : Holds τ p l₁ :=
  (append_iff.mp h).1
end
end MIPRE.TM.Interp.Holds

namespace MIPRE.TM.Interp.Holds
section
variable {τ : Tape} {p : ℤ}
theorem of_append_right {l₁ l₂ : List Sym} (h : Holds τ p (l₁ ++ l₂)) :
    Holds τ (p + l₁.length) l₂ := (append_iff.mp h).2
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
/-- A silent run followed by a silent halt. -/
theorem HaltsIn.after {c c' : Cfg input} {n m : ℕ} (h : Reach c n c' []) (h' : HaltsIn c' m) :
    HaltsIn c (n + m) := by
  unfold HaltsIn at *
  rw [configs_add, outputString_add_eq_append, h.1, h.2, h'.2]
  exact ⟨h'.1, rfl⟩
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
theorem Unary.push {τ : Tape} {n : ℕ} (h : Unary τ n) :
    Unary (Function.update τ n (some .one)) (n + 1) := by
  refine ⟨fun k hk => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · simp only [List.length_replicate] at hk
    by_cases hk' : k = n
    · subst hk'; simp
    · rw [Function.update_of_ne (by omega)]
      have := h.1 k (by simp; omega)
      simpa using this
  · rw [Function.update_of_ne (by omega)]; exact h.2.1 q (by omega)
  · rw [Function.update_of_ne (by omega)]; exact h.2.2 q hq
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
theorem frameRepr_eq (f : Frame) : frameRepr f = frameBody f ++ [.fr] := by
  cases f <;> simp [frameRepr, frameBody]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
/-- The first phase of `copyTree`: one pending subtree. -/
theorem copyTree_start {k : ProgId} {pc : Fin maxPc} {src : WT} {dst : Option WT} {ch : Bool}
    (hins : instrAt k pc = .copyTree src dst ch) (c : Cfg input) (hq : c.state = at_ k pc)
    (hcnt : Unary (c.workTapes CNT) 0) (hcp : c.workTapePos CNT = 0) :
    ∃ c', Reach c 1 c' [] ∧ c'.state = some ⟨k, pc, p1⟩ ∧ Untouched c c' [] [CNT] ∧
      Unary (c'.workTapes CNT) 1 ∧ c'.workTapePos CNT = 1 := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.ww_out, Act.base_out, Option.toList_none, Act.mw_next,
    Act.ww_next, Act.base_next, resolve_stay] at h
  refine ⟨_, h, rfl, ?_, ?_, ?_⟩
  · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have h2 : d ≠ CNT := by simpa using hd
      simp [Act.mw_works_of_ne _ h2, Act.ww_works_of_ne _ h2]⟩ _ _
  · rw [applyAct_workTapes_of_some _ _ _ CNT (s := some .one) (by simp), hcp]
    simpa using hcnt.push
  · simp [hcp]
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
/-- **`copyTree src (some t) true`** with an insufficient budget halts silently. -/
theorem exec_copyTree_charge_fail {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data)
    (c : Cfg input) (hq : c.state = at_ k pc) (hcnt : Unary (c.workTapes CNT) 0)
    (hcp : c.workTapePos CNT = 0) {r : ℕ} (hbud : Unary (c.workTapes BUD) r)
    (hbp : c.workTapePos BUD = r) (hr : r < v.size)
    (hsrc : Holds (c.workTapes src) (c.workTapePos src) (S v)) :
    HaltsIn c (4 * v.size + 1) := by
  obtain ⟨c₁, hr₁, hs₁, hu₁, hcnt₁, hcp₁⟩ := copyTree_start hins c hq hcnt hcp
  have := copyTree_scan_fail hins hpc hst hsc htc hsb htb v c₁ 1 r hs₁ le_rfl hcnt₁ (by simp [hcp₁])
    (by rw [hu₁.tapes (d := BUD) (by decide)]; exact hbud)
    (by rw [hu₁.pos (d := BUD) (by decide)]; exact hbp) hr
    (by rw [hu₁.tapes (d := src) (by simp [hsc]), hu₁.pos (d := src) (by simp [hsc])]; exact hsrc)
  rw [Nat.add_comm]
  exact HaltsIn.after hr₁ this
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
/-- A middle segment is held at its offset. -/
theorem holds_sub (h : TapeIs τ pos s) {l₁ l₂ l₃ : List Sym} (e : s.l = l₁ ++ l₂ ++ l₃) :
    Holds τ l₁.length l₂ := by
  have := h.holds
  rw [e] at this
  have := this.of_append_left.of_append_right
  rwa [zero_add] at this
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

namespace MIPRE.TM.Interp.TapeIs
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
theorem unary {n : ℕ} (h : TapeIs τ pos ⟨List.replicate n .one, n⟩) : Unary τ n :=
  ⟨h.holds, fun q hq => h.beyond q (by simpa using hq), fun q hq => h.before q hq⟩
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
theorem D_charge_fail (hins : instrAt k pc = .charge false) (hd : Desc c (at_ k pc) ds)
    (hb : ds BUD = ⟨[], 0⟩) : HaltsIn c 2 := by
  have hT := hd.tape BUD
  rw [hb] at hT
  exact exec_charge_one_fail hins c hd.state (by simpa using (TapeIs.unary (n := 0) hT))
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}
theorem D_copyTree_charge_fail {src t : WT} (hins : instrAt k pc = .copyTree src (some t) true)
    (hpc : pc.val + 1 < maxPc) (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD)
    (htb : t ≠ BUD) (hd : Desc c (at_ k pc) ds) (hcnt : ds CNT = ⟨[], 0⟩) {r : ℕ}
    (hbud : ds BUD = ⟨List.replicate r .one, r⟩) {v : Data} {l₁ l₂ : List Sym}
    (hsrc : (ds src).l = l₁ ++ S v ++ l₂) (hsp : (ds src).p = l₁.length) (hr : r < v.size) :
    HaltsIn c (4 * v.size + 1) := by
  have hS := hd.tape src
  have hN := hd.tape CNT
  rw [hcnt] at hN
  have hB := hd.tape BUD
  rw [hbud] at hB
  exact exec_copyTree_charge_fail hins hpc hst hsc htc hsb htb v c hd.state
    (by simpa using (TapeIs.unary (n := 0) hN)) (by rw [hd.pos, hcnt]; simp) hB.unary
    (by rw [hd.pos, hbud]) hr (by rw [hd.pos, hsp]; exact hS.holds_sub hsrc)
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
theorem case_evNil_fail {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evNil 0) ds)
    {env : Env} {k : List Frame}
    (hr : RepOf ds ⟨.ev .nil, env, k⟩ 0 4 (kontRepr k).length) :
    HaltsIn c (caseBound ⟨.ev .nil, env, k⟩ (ds X).l.length) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_rewind rfl (by decide) hd (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₁ hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_write rfl (by decide) hd₁ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₂
  obtain ⟨c₃, hr₃, hd₃⟩ := D_write rfl (by decide) hd₂ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₃
  have h4 := D_charge_fail rfl hd₃ (by simp <;> omega)
  exact (HaltsIn.after (((hr₁.trans hr₂).trans hr₃).cast_out (by simp <;> omega)) h4).mono
    (by simp only [caseBound]; omega)
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem case_evVar_fail {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evVar 0) ds)
    {i : ℕ} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.var i), env, k⟩ r 2 (kontRepr k).length)
    (hlt : r < (Env.get env i).size + 1) :
    HaltsIn c (caseBound ⟨.ev (.var i), env, k⟩ (ds X).l.length) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd
  have hvl := size_get_le env i
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₂ hd₂
  obtain ⟨n₃, hn₃, c₃, hr₃, hd₃⟩ := D_getEnv rfl (by decide) hd₂ (env := env) (by simp <;> omega) (i := i)
    (l₁ := [.zero, .one, .zero]) (l₂ := g) (by simp <;> omega) (by simp <;> omega) (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₃
  obtain ⟨c₄, hr₄, hd₄⟩ := D_rewind rfl (by decide) hd₃ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₄ hd₄
  obtain ⟨c₅, hr₅, hd₅⟩ := D_rewind rfl (by decide) hd₄ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₅ hd₅
  obtain ⟨c₆, hr₆, hd₆⟩ := D_write rfl (by decide) hd₅ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₆
  have hR : Reach c _ c₆ [] :=
    (((((hr₁.trans hr₂).trans hr₃).trans hr₄).trans hr₅).trans hr₆).cast_out (by simp <;> omega)
  rcases Nat.lt_or_ge r (Env.get env i).size with hr' | hr'
  · have h7 := D_copyTree_charge_fail rfl (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) hd₆ (by simp <;> omega) (r := r) (by simp <;> omega) (v := Env.get env i) (l₁ := [])
      (l₂ := (ds X).l.drop (S (Env.get env i)).length) (by simp <;> omega) (by simp <;> omega) hr'
    refine (HaltsIn.after hR h7).mono ?_
    simp only [caseBound, sz, ctrlRepr_var, List.length_cons, List.length_append, length_S_ofNat]
    omega
  · have hr0 : r = (Env.get env i).size := by omega
    subst hr0
    obtain ⟨n₇, hn₇, c₇, hr₇, hd₇⟩ := D_copyTree_charge rfl (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hd₆ (by simp <;> omega) (r := (Env.get env i).size) (by simp <;> omega)
      (v := Env.get env i) (l₁ := []) (l₂ := (ds X).l.drop (S (Env.get env i)).length) (by simp <;> omega) (by simp <;> omega)
      (by simp <;> omega) le_rfl
    try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₇
    have h8 := D_charge_fail rfl hd₇ (by simp <;> omega)
    refine (HaltsIn.after (hR.trans hr₇ |>.cast_out (by simp <;> omega)) h8).mono ?_
    simp only [caseBound, sz, ctrlRepr_var, List.length_cons, List.length_append, length_S_ofNat]
    omega
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem case_evConst_fail {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .evConst 0) ds)
    {d : Data} {env : Env} {k : List Frame} {r : ℕ}
    (hr : RepOf ds ⟨.ev (.const d), env, k⟩ r 14 (kontRepr k).length) (hlt : r < d.size) :
    HaltsIn c (caseBound ⟨.ev (.const d), env, k⟩ (ds X).l.length) := by
  obtain ⟨g, hds⟩ := hr.eq
  have hX := hr.scratch
  rw [hds] at hd
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd
  obtain ⟨c₁, hr₁, hd₁⟩ := D_move_right rfl (by decide) hd
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hd₁
  obtain ⟨c₂, hr₂, hd₂⟩ := D_rewind rfl (by decide) hd₁ (by simp <;> omega)
  try simp only [Function.update_idem, Function.update_self, Function.update_of_ne, ne_eq, not_false_eq_true, Nat.reduceAdd, C_ne_E, C_ne_K, C_ne_X, C_ne_CNT, C_ne_BUD, E_ne_C, E_ne_K, E_ne_X, E_ne_CNT, E_ne_BUD, K_ne_C, K_ne_E, K_ne_X, K_ne_CNT, K_ne_BUD, X_ne_C, X_ne_E, X_ne_K, X_ne_CNT, X_ne_BUD, CNT_ne_C, CNT_ne_E, CNT_ne_K, CNT_ne_X, CNT_ne_BUD, BUD_ne_C, BUD_ne_E, BUD_ne_K, BUD_ne_X, BUD_ne_CNT, overwrite_zero, overwrite_cons_succ, overwrite_cons_one_add, overwrite_append_nil', overwrite_append', List.cons_append, List.nil_append, List.append_nil, List.drop_succ_cons, List.drop_zero, List.length_cons, List.length_append, List.length_nil, List.length_singleton, length_S, length_S_ofNat, Nat.add_zero, Nat.zero_add, List.drop_left', Nat.add_sub_cancel, Data.size_nil, Data.size_cons, Data.size_ofNat, S_cons, S_nil, ctrlRepr_var, ctrlRepr_nil, ctrlRepr_cons, ctrlRepr_elim, ctrlRepr_let, ctrlRepr_loop, ctrlRepr_const, ctrlRepr_ret] at hr₂ hd₂
  have h3 := D_copyTree_charge_fail rfl (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hd₂ (by simp <;> omega) (r := r) (by simp <;> omega) (v := d)
    (l₁ := [.zero, .one, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .one, .zero, .one, .zero,
      .zero]) (l₂ := g) (by simp <;> omega) (by simp <;> omega) hlt
  refine (HaltsIn.after ((hr₁.trans hr₂).cast_out (by simp <;> omega)) h3).mono ?_
  simp only [caseBound, sz, ctrlRepr_const, List.length_cons, List.length_append, length_S]
  omega
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem PreTo.charge_fail {c : Cfg input} {B : ℕ} {k : ProgId} {pc : Fin maxPc} {m' : Machine.Cfg}
    {pC pK xl : ℕ} (h : PreTo c B (at_ k pc) m' 0 pC pK xl) (hins : instrAt k pc = .charge false) :
    HaltsIn c (B + 2) := by
  obtain ⟨n, hn, c', ds', hr, hd, hrep, hxl⟩ := h
  exact (HaltsIn.after hr (D_charge_fail hins hd (by simpa using hrep.bud))).mono (by omega)
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem _root_.solution {c : Cfg input} {ds : WT → TapeSt} (hd : Desc c (at_ .dispatch 0) ds)
    {m : Machine.Cfg} {r : ℕ}
    (hr : RepOf ds m r (ctrlRepr m.ctrl).length (kontRepr m.kont).length)
    (hnf : ∀ v, m.ctrl = .ret v → m.kont ≠ []) (hcost : r < stepCost m) :
    HaltsIn c (stepBound m (ds X).l.length) := by
  obtain ⟨ctrl, env, k⟩ := m
  cases ctrl with
  | ev p =>
    obtain ⟨n₁, hn₁₀, hn₁, c₁, ds₁, hr₁, hd₁, hrep₁, hxl₁⟩ := dispatch_ev hd hr
    have hmono : caseBound ⟨.ev p, env, k⟩ (ds₁ X).l.length ≤ caseBound ⟨.ev p, env, k⟩ (ds X).l.length := by
      simp only [caseBound]; omega
    cases p with
    | var i =>
      simp only [stepCost] at hcost
      refine (HaltsIn.after hr₁ (case_evVar_fail hd₁ hrep₁ hcost)).mono ?_
      simp only [stepBound, sz]; omega
    | nil =>
      simp only [stepCost] at hcost
      obtain rfl : r = 0 := by omega
      refine (HaltsIn.after hr₁ (case_evNil_fail hd₁ hrep₁)).mono ?_
      simp only [stepBound, sz]; omega
    | const d =>
      simp only [stepCost] at hcost
      refine (HaltsIn.after hr₁ (case_evConst_fail hd₁ hrep₁ hcost)).mono ?_
      simp only [stepBound, sz]; omega
    | cons h t =>
      simp only [stepCost] at hcost
      obtain rfl : r = 0 := by omega
      refine (HaltsIn.after hr₁ ((case_evCons hd₁ hrep₁).charge_fail rfl)).mono ?_
      simp only [stepBound, sz]; omega
    | elim i n cc =>
      simp only [stepCost] at hcost
      obtain rfl : r = 0 := by omega
      rcases hv : Env.get env i with _ | ⟨a, b⟩
      · refine (HaltsIn.after hr₁ ((case_evElim_nil hd₁ hrep₁ hv).charge_fail rfl)).mono ?_
        simp only [stepBound, sz]; omega
      · refine (HaltsIn.after hr₁ ((case_evElim_cons hd₁ hrep₁ hv).charge_fail rfl)).mono ?_
        simp only [stepBound, sz]; omega
    | let_ e b =>
      simp only [stepCost] at hcost
      obtain rfl : r = 0 := by omega
      refine (HaltsIn.after hr₁ ((case_evLet hd₁ hrep₁).charge_fail rfl)).mono ?_
      simp only [stepBound, sz]; omega
    | loop b => simp [stepCost] at hcost
  | ret v =>
    cases k with
    | nil => exact absurd rfl (hnf v rfl)
    | cons f k =>
      obtain ⟨n₁, hn₁₀, hn₁, c₁, ds₁, hr₁, hd₁, hrep₁, hxl₁⟩ := dispatch_ret hd hr
      have hmono : caseBound ⟨.ret v, env, f :: k⟩ (ds₁ X).l.length ≤
          caseBound ⟨.ret v, env, f :: k⟩ (ds X).l.length := by
        simp only [caseBound]; omega
      have hfb : (frameBody f).length ≤ (kontRepr (f :: k)).length := by
        rw [kontRepr_cons', List.length_append, List.length_append]; omega
      cases f with
      | cons1 t env' => simp [stepCost] at hcost
      | cons2 a => simp [stepCost] at hcost
      | let1 b env' => simp [stepCost] at hcost
      | loop1 b env' =>
        simp only [stepCost] at hcost
        obtain rfl : r = 0 := by omega
        rcases v with _ | ⟨_ | ⟨y, z⟩, v'⟩
        · refine (HaltsIn.after hr₁ ((case_retLoopNil hd₁ hrep₁).charge_fail rfl)).mono ?_
          simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
        · refine (HaltsIn.after hr₁ ((case_retLoopStop hd₁ hrep₁).charge_fail rfl)).mono ?_
          simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
        · refine (HaltsIn.after hr₁ ((case_retLoopCont hd₁ hrep₁).charge_fail rfl)).mono ?_
          simp only [stepBound, sz, ctrlRepr_ret, List.length_cons, length_S] at hfb ⊢; omega
end MIPRE.TM.Interp
