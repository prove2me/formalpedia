-- Prove2me | solution 1 for MIPRE.TM.Interp.D_getEnv
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:55:39.071242+00:00
-- url     : https://prove2.me/submissions/d231cff9-e077-46a0-ba7e-0556784a755e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Desc.lean (solution of MIPRE.TM.Interp.D_getEnv);
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
import Theorems.Thm_MIPRE_TM_Interp_exec_getEnv

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
theorem envTape {env : Env} {p : ℕ} (h : TapeIs τ pos ⟨envRepr env, p⟩) : EnvTape τ env :=
  ⟨h.holds, fun q hq => h.before q hq, fun q hq => h.beyond q hq⟩
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
theorem _root_.solution (hins : instrAt k pc = .getEnv) (hpc : pc.val + 1 < maxPc)
    (hd : Desc c (at_ k pc) ds) {env : Env} (hE : ds E = ⟨envRepr env, (envRepr env).length⟩)
    {i : ℕ} {l₁ l₂ : List Sym} (hC : (ds C).l = l₁ ++ S (Data.ofNat i) ++ l₂)
    (hCp : (ds C).p = l₁.length) (hX : (ds X).p ≤ (ds X).l.length) :
    ∃ n ≤ 3 * i + 3 * (envRepr env).length + 9, ∃ c', Reach c n c' [] ∧
      Desc c' (next_ k pc hpc)
        (Function.update (Function.update ds C ⟨(ds C).l, l₁.length + (2 * i + 1)⟩) X
          ⟨overwrite (ds X).l (ds X).p (S (Env.get env i)), (ds X).p + (S (Env.get env i)).length⟩) := by
  have hTE := hd.tape E
  rw [hE] at hTE
  have hTC := hd.tape C
  have hTX := hd.tape X
  obtain ⟨n, hn, c', hr, hs, hu, hCt, hCp', hEt, hEp', hde⟩ := exec_getEnv hins hpc env i c hd.state
    hTE.envTape (by rw [hd.pos, hE]) (by rw [hd.pos, hCp]; exact hTC.holds_sub hC)
  refine ⟨n, hn, c', hr, hd.of_untouched hu hs ?_ ?_⟩
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at ht'
    rcases ht' with rfl | rfl | rfl
    · rw [Function.update_of_ne (by decide), Function.update_self]
      exact hTC.of_same hCt (by rw [hCp', hd.pos, hCp]; push_cast; ring)
    · rw [Function.update_of_ne (by decide), Function.update_of_ne (by decide), hE]
      exact hTE.of_same hEt (by rw [hEp'])
    · rw [Function.update_self]
      refine hTX.of_overwrite hX ?_ ?_ ?_
      · rw [← hd.pos]; exact hde.holds
      · intro q hq; exact hde.outside q (by rw [hd.pos]; exact hq)
      · rw [hde.pos, hd.pos]; push_cast; ring
  · intro t' ht'
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, not_or] at ht'
    rw [Function.update_of_ne ht'.2.2, Function.update_of_ne ht'.1]
end MIPRE.TM.Interp
