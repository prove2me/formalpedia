-- Prove2me | solution 1 for MIPRE.TM.Interp.scan_leftToMarker
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:53:04.023793+00:00
-- url     : https://prove2.me/submissions/48b7279a-4089-4452-8e4d-71f42e54f1f2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Routines.lean (solution of MIPRE.TM.Interp.scan_leftToMarker);
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem _root_.solution {k : ProgId} {pc : Fin maxPc} {m : Sym} {t : WT}
    (hins : instrAt k pc = .leftToMarker m t) (hpc : pc.val + 1 < maxPc) (l : List Sym) :
    ∀ (c : Cfg input), c.state = some ⟨k, pc, p1⟩ →
      Holds (c.workTapes t) (c.workTapePos t + 1 - l.length) l → (∀ s ∈ l, s ≠ m) →
      (c.workTapes t (c.workTapePos t - l.length) = some m ∨
        c.workTapes t (c.workTapePos t - l.length) = none) →
    ∃ c', Reach c (l.length + 1) c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [t] ∧
      c'.workTapes t = c.workTapes t ∧ c'.workTapePos t = c.workTapePos t - l.length + 1 := by
  induction l using List.reverseRecOn with
  | nil =>
    intro c hq _ _ hend
    have h := step_instr hq hins
    simp only [List.length_nil, Nat.cast_zero, sub_zero] at hend
    have hact : execInstr (.leftToMarker m t) p1 c.inputSymbols c.workTapeSymbols =
        (Act.base .adv).mw t 1 := by
      simp only [execInstr, workTapeSymbols_eq]
      rcases hend with h1 | h1 <;> simp [h1]
    rw [hact] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next] at h
    refine ⟨_, h, by simp [resolve_adv k pc hpc], ?_, ?_, ?_⟩
    · exact untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    · rw [applyAct_workTapes_of_none _ _ _ t (by simp)]
    · simp
  | append_singleton l a ih =>
    intro c hq hl hm hend
    have hlen : ((l ++ [a]).length : ℤ) = l.length + 1 := by simp
    have ha : c.workTapes t (c.workTapePos t) = some a := by
      have := hl.of_append_right
      rw [Holds.singleton_iff] at this
      convert this using 2
      rw [hlen]; ring
    have h := step_instr hq hins
    have hact : execInstr (.leftToMarker m t) p1 c.inputSymbols c.workTapeSymbols =
        (Act.base (.stay p1)).mw t (-1) := by
      simp only [execInstr, workTapeSymbols_eq, ha]
      rw [if_neg (hm a (by simp))]
    rw [hact] at h
    simp only [Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
      resolve_stay] at h
    set c₁ := applyAct ((Act.base (.stay p1)).mw t (-1)) (some ⟨k, pc, p1⟩) c with hc₁
    have hu : Untouched c c₁ [] [t] :=
      untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
        have : d ≠ t := by simpa using hd
        simp [Act.mw_works_of_ne _ this]⟩ _ _
    have htape : c₁.workTapes t = c.workTapes t := by
      rw [hc₁, applyAct_workTapes_of_none _ _ _ t (by simp)]
    have hpos : c₁.workTapePos t = c.workTapePos t - 1 := by simp [hc₁]; ring
    have hl' : Holds (c₁.workTapes t) (c₁.workTapePos t + 1 - l.length) l := by
      rw [htape, hpos]
      have := hl.of_append_left
      convert this using 1
      rw [hlen]; ring
    have hend' : c₁.workTapes t (c₁.workTapePos t - l.length) = some m ∨
        c₁.workTapes t (c₁.workTapePos t - l.length) = none := by
      rw [htape, hpos]
      convert hend using 3 <;> (rw [hlen]; ring)
    obtain ⟨c', hr, hst, hu', htape', hpos'⟩ := ih c₁ (by simp [hc₁]) hl' (fun s hs => hm s (by simp [hs])) hend'
    refine ⟨c', ((h.trans hr).cast_n (by simp; omega)).cast_out (List.nil_append _), hst,
      (hu.trans hu').mono (by simp) (by simp), htape'.trans htape, ?_⟩
    rw [hpos', hpos, hlen]; ring
end MIPRE.TM.Interp
