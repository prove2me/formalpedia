-- Prove2me | solution 1 for MIPRE.TM.Interp.TapeIs.of_overwrite
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:50:26.683468+00:00
-- url     : https://prove2.me/submissions/1ac29e37-e042-4f95-9a7c-00ef84c560df

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Desc.lean (solution of MIPRE.TM.Interp.TapeIs.of_overwrite);
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
theorem append {l₁ l₂ : List Sym} (h₁ : Holds τ p l₁) (h₂ : Holds τ (p + l₁.length) l₂) :
    Holds τ p (l₁ ++ l₂) := append_iff.mpr ⟨h₁, h₂⟩
end
end MIPRE.TM.Interp.Holds

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
theorem length_overwrite {l : List Sym} {p : ℕ} (hp : p ≤ l.length) (w : List Sym) :
    (overwrite l p w).length = max l.length (p + w.length) := by
  simp [overwrite]; omega
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp.TapeIs
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {τ : Tape} {pos : ℤ} {s : TapeSt}
theorem _root_.solution {l : List Sym} {p : ℕ} (h : TapeIs τ pos ⟨l, p⟩) (hp : p ≤ l.length)
    {τ' : Tape} {pos' : ℤ} {p' : ℕ} {w : List Sym} (hw : Holds τ' p w)
    (hout : ∀ q : ℤ, (q < p ∨ (p : ℤ) + w.length ≤ q) → τ' q = τ q) (hpos : pos' = p') :
    TapeIs τ' pos' ⟨overwrite l p w, p'⟩ := by
  have hh : Holds τ 0 l := h.holds
  have hbf : ∀ q : ℤ, q < 0 → τ q = none := h.before
  have hby : ∀ q : ℤ, (l.length : ℤ) ≤ q → τ q = none := h.beyond
  refine ⟨?_, ?_, ?_, hpos⟩
  · show Holds τ' 0 (l.take p ++ w ++ l.drop (p + w.length))
    refine Holds.append (Holds.append ?_ ?_) ?_
    · intro k hk
      rw [List.length_take] at hk
      rw [zero_add, hout k (Or.inl (by omega)), List.getElem_take]
      have := hh k (by omega)
      rwa [zero_add] at this
    · rw [zero_add, List.length_take, min_eq_left hp]; exact hw
    · intro k hk
      rw [List.length_drop] at hk
      rw [List.length_append, List.length_take, min_eq_left hp, List.getElem_drop]
      have := hh (p + w.length + k) (by omega)
      rw [zero_add] at this
      rw [hout _ (Or.inr (by push_cast; omega))]
      convert this using 2
      push_cast; ring
  · intro q hq
    rw [hout q (Or.inl (by omega))]
    exact hbf q hq
  · intro q hq
    show τ' q = none
    rw [length_overwrite hp] at hq
    rw [hout q (Or.inr (by push_cast at hq ⊢; omega))]
    exact hby q (by push_cast at hq ⊢; omega)
end MIPRE.TM.Interp.TapeIs
