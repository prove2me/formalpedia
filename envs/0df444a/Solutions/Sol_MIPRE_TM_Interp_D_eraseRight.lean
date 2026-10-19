-- Prove2me | solution 1 for MIPRE.TM.Interp.D_eraseRight
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:55:57.2505+00:00
-- url     : https://prove2.me/submissions/329cc992-7881-41c0-9aff-ba9c8f25c989

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Desc.lean (solution of MIPRE.TM.Interp.D_eraseRight);
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
import Theorems.Thm_MIPRE_TM_Interp_TapeIs_of_truncate
import Theorems.Thm_MIPRE_TM_Interp_exec_eraseRight

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
theorem of_append_right {l₁ l₂ : List Sym} (h : Holds τ p (l₁ ++ l₂)) :
    Holds τ (p + l₁.length) l₂ := (append_iff.mp h).2
end
end MIPRE.TM.Interp.Holds

namespace MIPRE.TM.Interp.Reach
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem cast_n {c c' : Cfg input} {n n' : ℕ} {out : List Sym} (h : Reach c n c' out)
    (e : n = n') : Reach c n' c' out := e ▸ h
end
end MIPRE.TM.Interp.Reach

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
/-- The tail from `n`. -/
theorem holds_drop (h : TapeIs τ pos s) (n : ℕ) : Holds τ n (s.l.drop n) := by
  have := h.holds
  rw [← List.take_append_drop n s.l] at this
  have := this.of_append_right
  by_cases hn : n ≤ s.l.length
  · rwa [zero_add, List.length_take, min_eq_left hn] at this
  · rw [List.drop_of_length_le (by omega)]; exact Holds.nil
end
end MIPRE.TM.Interp.TapeIs

namespace MIPRE.TM.Interp.TapeIs
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
theorem blank_after_drop (h : TapeIs τ pos s) (n : ℕ) :
    τ (n + (s.l.drop n).length) = none := by
  apply h.beyond
  simp only [List.length_drop]; omega
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
theorem _root_.solution {t : WT} (hins : instrAt k pc = .eraseRight t) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) (hp : (ds t).p ≤ (ds t).l.length)
    (hfr : ∀ s ∈ (ds t).l.drop (ds t).p, s ≠ .fr) :
    ∃ c', Reach c (2 * ((ds t).l.length - (ds t).p) + 1) c' [] ∧
      Desc c' (next_ k pc hpc) (Function.update ds t ⟨(ds t).l.take (ds t).p, (ds t).p⟩) := by
  have hT := hd.tape t
  obtain ⟨c', hr, hs, hu, hout, hbl, hpos⟩ := exec_eraseRight hins hpc ((ds t).l.drop (ds t).p) c
    hd.state (by rw [hd.pos]; exact hT.holds_drop _) (by rw [hd.pos]; exact hT.blank_after_drop _)
  refine ⟨c', hr.cast_n (by simp), hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_singleton] at ht'
    subst ht'
    rw [Function.update_self]
    refine hT.of_truncate (n := (ds t').p) hp ?_ ?_ (by rw [hpos, hd.pos])
    · intro q hq
      apply hout
      rw [hd.pos]
      simp only [List.length_drop]
      rcases hq with hq | hq
      · exact Or.inl hq
      · right; push_cast; omega
    · rw [hd.pos] at hbl
      simpa using hbl
  · intro t' ht'
    exact Function.update_of_ne (by simpa using ht') _ _
end MIPRE.TM.Interp
