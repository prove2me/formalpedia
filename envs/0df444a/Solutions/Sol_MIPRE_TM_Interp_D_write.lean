-- Prove2me | solution 1 for MIPRE.TM.Interp.D_write
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:51:48.337979+00:00
-- url     : https://prove2.me/submissions/66c0a38b-df31-42c0-8885-000e8a94ca27

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Desc.lean (solution of MIPRE.TM.Interp.D_write);
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
import Theorems.Thm_MIPRE_TM_Interp_TapeIs_of_overwrite

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem single (c : Cfg input) : Reach c 1 (U.step c) (U.outputSymbol c).toList := by
  refine ⟨configs_succ_eq_step'.trans (by simp), ?_⟩
  rw [outputString_succ, outputString, List.range_zero, List.flatMap_nil, List.nil_append,
    configs_zero]
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}
theorem _root_.solution {t : WT} {s : Sym} (hins : instrAt k pc = .write t s) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : (ds t).p ≤ (ds t).l.length) :
    ∃ c', Reach c 1 c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds t ⟨overwrite (ds t).l (ds t).p [s], (ds t).p + 1⟩) := by
  obtain ⟨c', hr, hs, hu, htape, hpos⟩ := exec_write hins hpc c hd.state
  refine ⟨c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    refine (hd.tape t').of_overwrite hp ?_ ?_ ?_
    · rw [Holds.singleton_iff, htape, ← hd.pos, Function.update_self]
    · intro q hq
      rw [htape, hd.pos, Function.update_of_ne (by simp only [List.length_singleton] at hq; omega)]
    · rw [hpos, hd.pos]; push_cast; ring
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _
end MIPRE.TM.Interp
