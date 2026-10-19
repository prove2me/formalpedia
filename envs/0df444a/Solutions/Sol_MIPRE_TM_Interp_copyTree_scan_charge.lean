-- Prove2me | solution 1 for MIPRE.TM.Interp.copyTree_scan_charge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:50:25.932808+00:00
-- url     : https://prove2.me/submissions/5af1c6ac-50c0-441f-b549-54bad8e5d1d5

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/CopyTreeCharge.lean (solution of MIPRE.TM.Interp.copyTree_scan_charge);
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
theorem head {s : Sym} {l : List Sym} (h : Holds τ p (s :: l)) : τ p = some s := (cons_iff.mp h).1
end
end MIPRE.TM.Interp.Holds

namespace MIPRE.TM.Interp.Holds
section
variable {τ : Tape} {p : ℤ}
theorem tail {s : Sym} {l : List Sym} (h : Holds τ p (s :: l)) : Holds τ (p + 1) l :=
  (cons_iff.mp h).2
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
theorem Unary.cell {τ : Tape} {n : ℕ} (h : Unary τ n) (q : ℤ) :
    τ q = if 0 ≤ q ∧ q < n then some .one else none := by
  split_ifs with hq
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, q = k := ⟨q.toNat, by omega⟩
    have := h.1 k (by simp; omega)
    simpa using this
  · by_cases h0 : q < 0
    · exact h.2.2 q h0
    · exact h.2.1 q (by omega)
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem Unary.pop {τ : Tape} {n : ℕ} (h : Unary τ (n + 1)) :
    Unary (Function.update τ n none) n := by
  refine ⟨fun k hk => ?_, fun q hq => ?_, fun q hq => ?_⟩
  · simp only [List.length_replicate] at hk
    rw [Function.update_of_ne (by omega)]
    have := h.1 k (by simp; omega)
    simpa using this
  · by_cases hq' : q = n
    · subst hq'; simp
    · rw [Function.update_of_ne hq']; exact h.2.1 q (by omega)
  · rw [Function.update_of_ne (by omega)]; exact h.2.2 q hq
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
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
theorem DstEff.trans {t : WT} {c c' c'' : Cfg input} {l l' : List Sym} (h : DstEff t c c' l)
    (h' : DstEff t c' c'' l') : DstEff t c c'' (l ++ l') where
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
variable {input : Fin 7 → List Sym}
theorem DstEff.cast {t : WT} {c c' : Cfg input} {l l' : List Sym} (h : DstEff t c c' l)
    (e : l = l') : DstEff t c c' l' := e ▸ h
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
/-- One written symbol. -/
theorem DstEff.single {t : WT} {c c' : Cfg input} {s : Sym}
    (htape : c'.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some s))
    (hpos : c'.workTapePos t = c.workTapePos t + 1) : DstEff t c c' [s] where
  holds := by rw [htape]; exact holds_update_self _ _ _
  outside q hq := by
    rw [htape, Function.update_of_ne]
    simp only [List.length_singleton, Nat.cast_one] at hq
    omega
  pos := by simp [hpos]
end
end MIPRE.TM.Interp

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
theorem _root_.solution {k : ProgId} {pc : Fin maxPc} {src t : WT}
    (hins : instrAt k pc = .copyTree src (some t) true) (hpc : pc.val + 1 < maxPc)
    (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD) (htb : t ≠ BUD) (v : Data) :
    ∀ (c : Cfg input) (d r : ℕ), c.state = some ⟨k, pc, p1⟩ → 1 ≤ d →
      Unary (c.workTapes CNT) d → c.workTapePos CNT = d →
      Unary (c.workTapes BUD) r → c.workTapePos BUD = r → v.size ≤ r →
      Holds (c.workTapes src) (c.workTapePos src) (S v) →
    ∃ n ≤ 4 * v.size, ∃ c', Reach c n c' [] ∧ c'.state = scanExit k pc hpc d ∧
      Untouched c c' [] [src, CNT, t, BUD] ∧
      c'.workTapes src = c.workTapes src ∧ c'.workTapePos src = c.workTapePos src + v.size ∧
      Unary (c'.workTapes CNT) (d - 1) ∧ c'.workTapePos CNT = d - 1 ∧
      Unary (c'.workTapes BUD) (r - v.size) ∧ c'.workTapePos BUD = ((r - v.size : ℕ) : ℤ) ∧
      DstEff t c c' (S v) := by
  have hcb : CNT ≠ BUD := by decide
  induction v with
  | nil =>
    intro c d r hq hd hcnt hcp hbud hbp hr hsrc
    simp only [Data.size_nil] at hr
    have hread : c.workTapes src (c.workTapePos src) = some .zero := by
      simpa using hsrc.head
    -- step 1
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, if_true, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h1
    set c₁ := applyAct ((((((Act.base (.stay p2)).mw src 1).mw CNT (-1)).mw BUD (-1)).ww t
      (some .zero)).mw t 1) (some ⟨k, pc, p2⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [src, CNT, t, BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        have h3 : d ≠ t := fun e => hd (by simp [e])
        have h4 : d ≠ BUD := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.mw_works_of_ne _ h3,
          Act.mw_works_of_ne _ h4, Act.ww_works_of_ne _ h3]⟩ _ _
    have hsrc₁ : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by
        simp [Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
          Act.mw_works_of_ne _ hsb])]
    have hsrcp₁ : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
        Act.mw_works_of_ne _ hsb]
    have hcnt₁ : c₁.workTapes CNT = c.workTapes CNT := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ CNT (by
        simp [Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
          Act.mw_works_of_ne _ hsc.symm, Act.mw_works_of_ne _ hcb])]
    have hcp₁ : c₁.workTapePos CNT = ((d - 1 : ℕ) : ℤ) := by
      simp [hc₁, Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
        Act.mw_works_of_ne _ hsc.symm, Act.mw_works_of_ne _ hcb, hcp]
      omega
    have hbud₁ : c₁.workTapes BUD = c.workTapes BUD := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ BUD (by
        simp [Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
          Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm,
          Act.ww_works_of_ne _ hcb.symm])]
    have hbp₁ : c₁.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by
      simp [hc₁, Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
        Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm, Act.ww_works_of_ne _ hcb.symm,
        hbp]
      omega
    have ht₁ : c₁.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some .zero) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ t (s := some .zero) (by simp)]
    have htp₁ : c₁.workTapePos t = c.workTapePos t + 1 := by simp [hc₁]
    -- step 2: the budget check, the counter pop
    have hbread : c₁.workTapes BUD (c₁.workTapePos BUD) = some .one := by
      rw [hbud₁, hbp₁, hbud.cell]; rw [if_pos]; omega
    have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p2) (by simp [hc₁]) hins
    simp only [execInstr, workTapeSymbols_eq, hbread, if_true, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h2
    set c₂ := applyAct ((((Act.base (.stay p3)).ww CNT none).mw CNT (-1)).ww BUD none)
      (some ⟨k, pc, p3⟩) c₁ with hc₂
    have hu₂ : Untouched c₁ c₂ [] [CNT, BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        have h4 : d ≠ BUD := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h2, Act.ww_works_of_ne _ h2, Act.ww_works_of_ne _ h4]⟩ _ _
    have hcnt₂ : Unary (c₂.workTapes CNT) (d - 1) := by
      rw [hc₂, applyAct_workTapes_of_some _ _ _ CNT (s := none) (by simp [Act.ww_works_of_ne _ hcb]),
        hcnt₁, hcp₁]
      have := hcnt
      rw [show d = d - 1 + 1 by omega] at this
      exact this.pop
    have hcp₂ : c₂.workTapePos CNT = (d : ℤ) - 2 := by
      simp [hc₂, hcp₁, Act.ww_works_of_ne _ hcb]; omega
    have hbud₂ : Unary (c₂.workTapes BUD) (r - 1) := by
      rw [hc₂, applyAct_workTapes_of_some _ _ _ BUD (s := none) (by simp), hbud₁, hbp₁]
      have := hbud
      rw [show r = r - 1 + 1 by omega] at this
      exact this.pop
    have hbp₂ : c₂.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by
      simp [hc₂, hbp₁, Act.mw_works_of_ne _ hcb.symm, Act.ww_works_of_ne _ hcb.symm]
    -- step 3
    have h3 := step_instr (c := c₂) (k := k) (pc := pc) (ph := p3) (by simp [hc₂]) hins
    simp only [execInstr, workTapeSymbols_eq] at h3
    rw [hcp₂, hcnt₂.cell] at h3
    have hu₃ : ∀ (n : Next) (c₀ : Cfg input) (q' : Option Ctl),
        Untouched c₀ (applyAct ((Act.base n).mw CNT 1) q' c₀) [] [CNT] := fun n c₀ q' =>
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h2 : d ≠ CNT := by simpa using hd
        simp [Act.mw_works_of_ne _ h2]⟩ _ _
    have hfin : ∀ (n : Next) (q' : Option Ctl),
        let c' := applyAct ((Act.base n).mw CNT 1) q' c₂
        Untouched c c' [] [src, CNT, t, BUD] ∧ c'.workTapes src = c.workTapes src ∧
        c'.workTapePos src = c.workTapePos src + (1 : ℕ) ∧ Unary (c'.workTapes CNT) (d - 1) ∧
        c'.workTapePos CNT = (d : ℤ) - 2 + 1 ∧ Unary (c'.workTapes BUD) (r - 1) ∧
        c'.workTapePos BUD = ((r - 1 : ℕ) : ℤ) ∧ DstEff t c c' [.zero] := by
      intro n q'
      refine ⟨((hu₁.trans hu₂).trans (hu₃ _ _ _)).mono (by simp) (by simp), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [applyAct_workTapes_of_none _ _ _ src (by simp [Act.mw_works_of_ne _ hsc]),
          hu₂.tapes (d := src) (by simp [hsc, hsb]), hsrc₁]
      · simp [Act.mw_works_of_ne _ hsc, hu₂.pos (d := src) (by simp [hsc, hsb]), hsrcp₁]
      · rw [applyAct_workTapes_of_none _ _ _ CNT (by simp)]; exact hcnt₂
      · simp [hcp₂]
      · rw [applyAct_workTapes_of_none _ _ _ BUD (by simp [Act.mw_works_of_ne _ hcb.symm])]
        exact hbud₂
      · simp [Act.mw_works_of_ne _ hcb.symm, hbp₂]
      · refine DstEff.single ?_ ?_
        · rw [applyAct_workTapes_of_none _ _ _ t (by simp [Act.mw_works_of_ne _ htc]),
            hu₂.tapes (d := t) (by simp [htc, htb]), ht₁]
        · simp [Act.mw_works_of_ne _ htc, hu₂.pos (d := t) (by simp [htc, htb]), htp₁]
    by_cases hd1 : d = 1
    · have hcell : (if 0 ≤ (d : ℤ) - 2 ∧ (d : ℤ) - 2 < ((d - 1 : ℕ) : ℤ) then some Sym.one
          else none) = none := by
        rw [if_neg]; omega
      rw [hcell] at h3
      simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next] at h3
      obtain ⟨hu, hs, hsp, hc, hcp', hb, hbp', hde⟩ := hfin .adv (resolve k pc .adv)
      refine ⟨3, by simp, _, ((h1.trans h2).trans h3).cast_out (by simp),
        by simp [scanExit, hd1, resolve_adv k pc hpc], hu, hs, by rw [hsp]; simp, hc,
        by rw [hcp']; omega, by simpa using hb, by simpa using hbp', by rw [S_nil]; exact hde⟩
    · have hcell : (if 0 ≤ (d : ℤ) - 2 ∧ (d : ℤ) - 2 < ((d - 1 : ℕ) : ℤ) then some Sym.one
          else none) = some Sym.one := by
        rw [if_pos]; omega
      rw [hcell] at h3
      simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
        resolve_stay] at h3
      obtain ⟨hu, hs, hsp, hc, hcp', hb, hbp', hde⟩ := hfin (.stay p1) (some ⟨k, pc, p1⟩)
      refine ⟨3, by simp, _, ((h1.trans h2).trans h3).cast_out (by simp),
        by simp [scanExit, hd1], hu, hs, by rw [hsp]; simp, hc,
        by rw [hcp']; omega, by simpa using hb, by simpa using hbp', by rw [S_nil]; exact hde⟩
  | cons a b iha ihb =>
    intro c d r hq hd hcnt hcp hbud hbp hr hsrc
    simp only [Data.size_cons] at hr
    rw [S_cons] at hsrc
    have hread : c.workTapes src (c.workTapePos src) = some .one := hsrc.head
    -- step 1: the `1`
    have h1 := step_instr hq hins
    simp only [execInstr, workTapeSymbols_eq, hread, if_true, Act.mw_out, Act.ww_out, Act.base_out,
      Option.toList_none, Act.mw_next, Act.ww_next, Act.base_next, resolve_stay] at h1
    set c₁ := applyAct (((((((Act.base (.stay p4)).mw src 1).ww CNT (some .one)).mw CNT 1).mw BUD
      (-1)).ww t (some .one)).mw t 1) (some ⟨k, pc, p4⟩) c with hc₁
    have hu₁ : Untouched c c₁ [] [src, CNT, t, BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h1 : d ≠ src := fun e => hd (by simp [e])
        have h2 : d ≠ CNT := fun e => hd (by simp [e])
        have h3 : d ≠ t := fun e => hd (by simp [e])
        have h4 : d ≠ BUD := fun e => hd (by simp [e])
        simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2, Act.mw_works_of_ne _ h3,
          Act.mw_works_of_ne _ h4, Act.ww_works_of_ne _ h3, Act.ww_works_of_ne _ h2]⟩ _ _
    have hsrc₁ : c₁.workTapes src = c.workTapes src := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ src (by
        simp [Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
          Act.ww_works_of_ne _ hsc, Act.mw_works_of_ne _ hsb])]
    have hsrcp₁ : c₁.workTapePos src = c.workTapePos src + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ hst, Act.ww_works_of_ne _ hst, Act.mw_works_of_ne _ hsc,
        Act.ww_works_of_ne _ hsc, Act.mw_works_of_ne _ hsb]
    have hcnt₁ : Unary (c₁.workTapes CNT) (d + 1) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ CNT (s := some .one) (by
        simp [Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
          Act.mw_works_of_ne _ hcb]), hcp]
      exact hcnt.push
    have hcp₁ : c₁.workTapePos CNT = d + 1 := by
      simp [hc₁, Act.mw_works_of_ne _ htc.symm, Act.ww_works_of_ne _ htc.symm,
        Act.mw_works_of_ne _ hcb, hcp]
    have hbud₁ : c₁.workTapes BUD = c.workTapes BUD := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ BUD (by
        simp [Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
          Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm,
          Act.ww_works_of_ne _ hcb.symm])]
    have hbp₁ : c₁.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by
      simp [hc₁, Act.mw_works_of_ne _ htb.symm, Act.ww_works_of_ne _ htb.symm,
        Act.mw_works_of_ne _ hsb.symm, Act.mw_works_of_ne _ hcb.symm, Act.ww_works_of_ne _ hcb.symm,
        hbp]
      omega
    have ht₁ : c₁.workTapes t = Function.update (c.workTapes t) (c.workTapePos t) (some .one) := by
      rw [hc₁, applyAct_workTapes_of_some _ _ _ t (s := some .one) (by simp)]
    have htp₁ : c₁.workTapePos t = c.workTapePos t + 1 := by simp [hc₁]
    have hde₁ : DstEff t c c₁ [.one] := DstEff.single ht₁ htp₁
    -- step 2: the budget check
    have hbread : c₁.workTapes BUD (c₁.workTapePos BUD) = some .one := by
      rw [hbud₁, hbp₁, hbud.cell]; rw [if_pos]; omega
    have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p4) (by simp [hc₁]) hins
    simp only [execInstr, workTapeSymbols_eq, hbread, Act.ww_out, Act.base_out, Option.toList_none,
      Act.ww_next, Act.base_next, resolve_stay] at h2
    set c₂ := applyAct ((Act.base (.stay p1)).ww BUD none) (some ⟨k, pc, p1⟩) c₁ with hc₂
    have hu₂ : Untouched c₁ c₂ [] [BUD] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have h4 : d ≠ BUD := by simpa using hd
        simp [Act.ww_works_of_ne _ h4]⟩ _ _
    have hbud₂ : Unary (c₂.workTapes BUD) (r - 1) := by
      rw [hc₂, applyAct_workTapes_of_some _ _ _ BUD (s := none) (by simp), hbud₁, hbp₁]
      have := hbud
      rw [show r = r - 1 + 1 by omega] at this
      exact this.pop
    have hbp₂ : c₂.workTapePos BUD = ((r - 1 : ℕ) : ℤ) := by simp [hc₂, hbp₁]
    -- the left subtree
    obtain ⟨na, hna, c₃, hr₃, hst₃, hu₃, hsrc₃, hsrcp₃, hcnt₃, hcp₃, hbud₃, hbp₃, hde₃⟩ :=
      iha c₂ (d + 1) (r - 1) (by simp [hc₂]) (by omega)
        (by rw [hu₂.tapes (d := CNT) (by simp [hcb])]; exact hcnt₁)
        (by rw [hu₂.pos (d := CNT) (by simp [hcb]), hcp₁]; push_cast; ring) hbud₂ hbp₂ (by omega)
        (by rw [hu₂.tapes (d := src) (by simp [hsb]), hu₂.pos (d := src) (by simp [hsb]), hsrc₁,
          hsrcp₁]; exact hsrc.tail.of_append_left)
    have hst₃' : c₃.state = some ⟨k, pc, p1⟩ := by
      rw [hst₃, scanExit, if_neg (by omega)]
    -- the right subtree
    obtain ⟨nb, hnb, c₄, hr₄, hst₄, hu₄, hsrc₄, hsrcp₄, hcnt₄, hcp₄, hbud₄, hbp₄, hde₄⟩ :=
      ihb c₃ d (r - 1 - a.size) hst₃' hd (by simpa using hcnt₃) (by rw [hcp₃]; simp) hbud₃ hbp₃
        (by omega)
        (by
          rw [hsrc₃, hsrcp₃, hu₂.tapes (d := src) (by simp [hsb]), hu₂.pos (d := src) (by simp [hsb]),
            hsrc₁, hsrcp₁]
          have := hsrc.tail.of_append_right
          rw [length_S] at this
          convert this using 1)
    refine ⟨2 + na + nb, by rw [Data.size_cons]; omega, c₄, ?_, hst₄, ?_, ?_, ?_, hcnt₄, hcp₄,
      ?_, ?_, ?_⟩
    · exact (((h1.trans h2).trans hr₃).trans hr₄).cast_out (by simp)
    · exact (((hu₁.trans hu₂).trans hu₃).trans hu₄).mono (by simp) (by simp)
    · rw [hsrc₄, hsrc₃, hu₂.tapes (d := src) (by simp [hsb]), hsrc₁]
    · rw [hsrcp₄, hsrcp₃, hu₂.pos (d := src) (by simp [hsb]), hsrcp₁]
      simp only [Data.size_cons]; push_cast; ring
    · have e : r - (Data.cons a b).size = r - 1 - a.size - b.size := by
        rw [Data.size_cons]; omega
      rw [e]; exact hbud₄
    · have e : r - (Data.cons a b).size = r - 1 - a.size - b.size := by
        rw [Data.size_cons]; omega
      rw [hbp₄, e]
    · rw [S_cons]
      refine (hde₁.trans (?_ : DstEff t c₁ c₄ (S a ++ S b))).cast (by simp)
      refine DstEff.trans ?_ hde₄
      refine ⟨?_, ?_, ?_⟩
      · rw [← hu₂.pos (d := t) (by simp [htb])]; exact hde₃.holds
      · intro q hq'
        rw [hde₃.outside q (by rw [hu₂.pos (d := t) (by simp [htb])]; exact hq'),
          hu₂.tapes (d := t) (by simp [htb])]
      · rw [hde₃.pos, hu₂.pos (d := t) (by simp [htb])]
end MIPRE.TM.Interp
