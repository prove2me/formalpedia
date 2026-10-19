-- Prove2me | solution 1 for MIPRE.TM.Interp.exec_charge_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:53:30.260097+00:00
-- url     : https://prove2.me/submissions/8ea39917-2b61-4e4b-b845-b7aa8ee825e4

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Routines.lean (solution of MIPRE.TM.Interp.exec_charge_one);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Computability.Language
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Sign.Defs
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Cslib_Foundations_Data_RelatesInSteps
import Definitions.Def_MIPRE_Cslib_Computability_Machines_Turing_MultiTape_Deterministic
import Definitions.Def_MIPRE_TM_MultiInput_Deterministic
import Definitions.Def_MIPRE_TM_Interp_Instr
import Definitions.Def_MIPRE_TM_Interp_Machine
import Definitions.Def_MIPRE_TM_Interp_Tape
import Definitions.Def_MIPRE_TM_Interp_Reach
import Definitions.Def_MIPRE_TM_Interp_Routines

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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem _root_.solution {k : ProgId} {pc : Fin maxPc}
    (hins : instrAt k pc = .charge false) (hpc : pc.val + 1 < maxPc) (c : Cfg input)
    (hq : c.state = at_ k pc) {r : ℕ} (hb : Unary (c.workTapes BUD) (r + 1))
    (hpos : c.workTapePos BUD = r + 1) :
    ∃ c', Reach c 2 c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [BUD] ∧
      Unary (c'.workTapes BUD) r ∧ c'.workTapePos BUD = r := by
  have h := step_instr hq hins
  simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
    resolve_stay] at h
  set c₁ := applyAct ((Act.base (.stay p1)).mw BUD (-1)) (some ⟨k, pc, p1⟩) c with hc₁
  have hu : Untouched c c₁ [] [BUD] :=
    untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ BUD := by simpa using hd
      simp [Act.mw_works_of_ne _ this]⟩ _ _
  have htape : c₁.workTapes BUD = c.workTapes BUD := by
    rw [hc₁, applyAct_workTapes_of_none _ _ _ BUD (by simp)]
  have hpos₁ : c₁.workTapePos BUD = r := by simp [hc₁, hpos]
  have hread : c₁.workTapes BUD (c₁.workTapePos BUD) = some .one := by
    rw [htape, hpos₁, hb.cell]; simp
  have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p1) (by simp [hc₁]) hins
  simp only [execInstr, workTapeSymbols_eq, hread, if_false, Act.ww_out, Act.base_out,
    Option.toList_none, Act.ww_next, Act.base_next, Bool.false_eq_true] at h2
  refine ⟨_, (h.trans h2).cast_out (List.nil_append _), by simp [resolve_adv k pc hpc], ?_, ?_, ?_⟩
  · exact (hu.trans (untouched_applyAct (SI := []) (SW := [BUD]) ⟨fun j _ => rfl, fun d hd => by
      have : d ≠ BUD := by simpa using hd
      simp [Act.ww_works_of_ne _ this]⟩ _ _)).mono (by simp) (by simp)
  · rw [applyAct_workTapes_of_some _ _ _ BUD (s := none) (by simp), htape, hpos₁]
    exact hb.pop
  · simp [hpos₁]
end MIPRE.TM.Interp
