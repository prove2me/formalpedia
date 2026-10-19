-- Prove2me | solution 1 for MIPRE.TM.Interp.D_copyTree_charge
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:52:29.786955+00:00
-- url     : https://prove2.me/submissions/9bc4abb5-3ab1-4610-b30e-3c3de0655576

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Desc.lean (solution of MIPRE.TM.Interp.D_copyTree_charge);
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
import Theorems.Thm_MIPRE_TM_Interp_exec_copyTree_charge

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
theorem of_unary {n : ℕ} (hu : Unary τ n) (hpos : pos = n) :
    TapeIs τ pos ⟨List.replicate n .one, n⟩ :=
  ⟨hu.1, fun q hq => hu.2.2 q hq, fun q hq => hu.2.1 q (by simpa using hq), hpos⟩
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {k : ProgId} {pc : Fin maxPc} {c : Cfg input} {ds : WT → TapeSt}
theorem _root_.solution {src t : WT} (hins : instrAt k pc = .copyTree src (some t) true)
    (hpc : pc.val + 1 < maxPc) (hst : src ≠ t) (hsc : src ≠ CNT) (htc : t ≠ CNT) (hsb : src ≠ BUD)
    (htb : t ≠ BUD) (hd : Desc c (at_ k pc) ds) (hcnt : ds CNT = ⟨[], 0⟩) {r : ℕ}
    (hbud : ds BUD = ⟨List.replicate r .one, r⟩) {v : Data} {l₁ l₂ : List Sym}
    (hsrc : (ds src).l = l₁ ++ S v ++ l₂) (hsp : (ds src).p = l₁.length)
    (htp : (ds t).p ≤ (ds t).l.length) (hr : v.size ≤ r) :
    ∃ n ≤ 4 * v.size + 1, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc)
        (Function.update (Function.update (Function.update ds src ⟨(ds src).l, l₁.length + v.size⟩) t
          ⟨overwrite (ds t).l (ds t).p (S v), (ds t).p + v.size⟩) BUD
          ⟨List.replicate (r - v.size) .one, r - v.size⟩) := by
  have hS := hd.tape src
  have hT := hd.tape t
  have hN := hd.tape CNT
  rw [hcnt] at hN
  have hB := hd.tape BUD
  rw [hbud] at hB
  obtain ⟨n, hn, c', hr', hs, hu, hst', hsp', hcnt', hcp', hbud', hbp', hde⟩ :=
    exec_copyTree_charge hins hpc hst hsc htc hsb htb v c hd.state
      (by simpa using (TapeIs.unary (n := 0) hN)) (by rw [hd.pos, hcnt]; simp) hB.unary
      (by rw [hd.pos, hbud]) hr (by rw [hd.pos, hsp]; exact hS.holds_sub hsrc)
  refine ⟨n, hn, c', hr', hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl | rfl | rfl
    · rw [Function.update_of_ne hsb, Function.update_of_ne hst, Function.update_self]
      exact hS.of_same hst' (by rw [hsp', hd.pos, hsp]; push_cast; ring)
    · have hcb : CNT ≠ BUD := by decide
      rw [Function.update_of_ne hcb, Function.update_of_ne htc.symm, Function.update_of_ne hsc.symm,
        hcnt]
      have := TapeIs.of_unary hcnt' hcp'
      simpa using this
    · rw [Function.update_of_ne htb, Function.update_self]
      refine hT.of_overwrite htp ?_ ?_ ?_
      · rw [← hd.pos]; exact hde.holds
      · intro q hq; exact hde.outside q (by rw [hd.pos]; exact hq)
      · rw [hde.pos, hd.pos, length_S]; push_cast; ring
    · rw [Function.update_self]
      exact TapeIs.of_unary hbud' hbp'
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at ht'
    rw [Function.update_of_ne ht'.2.2.2, Function.update_of_ne ht'.2.2.1, Function.update_of_ne ht'.1]
end MIPRE.TM.Interp
