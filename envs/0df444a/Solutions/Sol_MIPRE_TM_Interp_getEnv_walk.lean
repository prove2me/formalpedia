-- Prove2me | solution 1 for MIPRE.TM.Interp.getEnv_walk
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:52:47.106443+00:00
-- url     : https://prove2.me/submissions/ce1d5d4e-3c04-4cd9-9a51-c3231d29ff4b

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/GetEnv.lean (solution of MIPRE.TM.Interp.getEnv_walk);
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
import Theorems.Thm_MIPRE_TM_Interp_EnvTape_suffix_cells
import Theorems.Thm_MIPRE_TM_Interp_getEnv_consume
import Theorems.Thm_MIPRE_TM_Interp_getEnv_copy5
import Theorems.Thm_MIPRE_TM_Interp_getEnv_scan3
import Theorems.Thm_MIPRE_TM_Interp_getEnv_scan4
import Theorems.Thm_MIPRE_TM_Interp_getEnv_toEnd

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
open MIPRE.Cost MIPRE.Cost.Machine
theorem S_cons (a b : Data) : S (.cons a b) = .one :: (S a ++ S b) := by
  simp [S, Data.toBits]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open MIPRE.Cost MIPRE.Cost.Machine
/-- The symbols of a value are bits. -/
theorem mem_S (v : Data) : ∀ s ∈ S v, s = .zero ∨ s = .one := by
  intro s hs
  simp only [S, bits, List.mem_map] at hs
  obtain ⟨b, -, rfl⟩ := hs
  cases b <;> simp
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
/-- The unary index `S(ofNat i)`: `(1 0)^i 0`. -/
theorem S_ofNat_succ (i : ℕ) : S (Data.ofNat (i + 1)) = .one :: .zero :: S (Data.ofNat i) := by
  simp [Data.ofNat, S_cons]
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
/-- The cells from `q` to the end of the environment. -/
theorem EnvTape.tail_cells {τ : Tape} {env : Env} (h : EnvTape τ env) (q : ℕ)
    (hq : q ≤ (envRepr env).length) :
    Holds τ q ((envRepr env).drop q) ∧ τ (q + ((envRepr env).drop q).length) = none := by
  refine ⟨?_, ?_⟩
  · have := h.holds
    rw [← List.take_append_drop q (envRepr env)] at this
    have h2 := this.of_append_right
    simpa [List.length_take, hq] using h2
  · apply h.beyond
    simp [List.length_drop]; omega
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
theorem Env.get_nil' (j : ℕ) : Env.get [] j = .nil := by simp
end
end MIPRE.TM.Interp

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
theorem _root_.solution {k : ProgId} {pc : Fin maxPc} (hins : instrAt k pc = .getEnv)
    (hpc : pc.val + 1 < maxPc) (env : Env) (j : ℕ) :
    ∀ (env' : Env) (c : Cfg input), c.state = some ⟨k, pc, p1⟩ →
      EnvTape (c.workTapes E) env → (∃ l₀, envRepr env = envRepr env' ++ l₀) →
      c.workTapePos E = (envRepr env').length - 1 →
      Holds (c.workTapes C) (c.workTapePos C) (S (Data.ofNat j)) →
    ∃ n ≤ 3 * j + 2 * (envRepr env).length + (envRepr env').length + 8,
    ∃ c', Reach c n c' [] ∧ c'.state = next_ k pc hpc ∧ Untouched c c' [] [C, E, X] ∧
      c'.workTapes C = c.workTapes C ∧ c'.workTapePos C = c.workTapePos C + (2 * j + 1 : ℕ) ∧
      c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = (envRepr env).length ∧
      DstEff X c c' (S (Env.get env' j)) := by
  have hCE : C ≠ E := by decide
  have hCX : C ≠ X := by decide
  have hEX : E ≠ X := by decide
  -- the out-of-range exit from `p6`: consume the index, write `nil`, move to the end
  have exit6 : ∀ (j : ℕ) (c : Cfg input), c.state = some ⟨k, pc, p6⟩ →
      EnvTape (c.workTapes E) env →
      c.workTapePos E = -1 → Holds (c.workTapes C) (c.workTapePos C) (S (Data.ofNat j)) →
      ∃ c', Reach c (2 * j + 1 + ((envRepr env).length + 1)) c' [] ∧ c'.state = next_ k pc hpc ∧
        Untouched c c' [] [C, E, X] ∧
        c'.workTapes C = c.workTapes C ∧ c'.workTapePos C = c.workTapePos C + (2 * j + 1 : ℕ) ∧
        c'.workTapes E = c.workTapes E ∧ c'.workTapePos E = (envRepr env).length ∧
        DstEff X c c' [.zero] := by
    intro j c hq hE hpos hC
    obtain ⟨c₁, hr₁, hs₁, hu₁, hC₁, hCp₁, hE₁, hEp₁, hde₁⟩ := getEnv_consume hins j c hq hC
    have hE₁' : EnvTape (c₁.workTapes E) env := by rw [hE₁]; exact hE
    obtain ⟨hhold, hend⟩ := hE₁'.tail_cells 0 (by omega)
    obtain ⟨c₂, hr₂, hs₂, hu₂, hE₂, hEp₂⟩ := getEnv_toEnd hins hpc p9 (Or.inr rfl) _ c₁ hs₁
      (by rw [hEp₁, hpos]; simpa using hhold) (by rw [hEp₁, hpos]; simpa using hend)
    refine ⟨c₂, ((hr₁.trans hr₂).cast_n (by simp)).cast_out (by simp), hs₂,
      (hu₁.trans hu₂).mono (by simp) (by simp), ?_, ?_, hE₂.trans hE₁, ?_, ?_⟩
    · rw [hu₂.tapes (d := C) (by decide), hC₁]
    · rw [hu₂.pos (d := C) (by decide), hCp₁]
    · rw [hEp₂, hEp₁, hpos]; simp
    · refine ⟨?_, ?_, ?_⟩
      · rw [hu₂.tapes (d := X) (by decide)]; exact hde₁.holds
      · intro q hq'; rw [hu₂.tapes (d := X) (by decide)]; exact hde₁.outside q hq'
      · rw [hu₂.pos (d := X) (by decide)]; exact hde₁.pos
  induction j with
  | zero =>
    intro env' c hq hE hpre hpos hC
    cases env' with
    | nil =>
      -- before the tape: out of range
      simp only [envRepr_nil, List.length_nil, Nat.cast_zero, zero_sub] at hpos
      have hread : c.workTapes E (c.workTapePos E) = none := by rw [hpos]; exact hE.before _ (by norm_num)
      have h := step_instr hq hins
      simp only [execInstr, workTapeSymbols_eq, hread, Act.base_out, Option.toList_none, Act.base_next,
        resolve_stay] at h
      set c₁ := applyAct (Act.base (.stay p6)) (some ⟨k, pc, p6⟩) c with hc₁
      have hu₁ : Untouched c c₁ [] [] := untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _
      obtain ⟨c', hr, hs, hu, hC', hCp', hE', hEp', hde⟩ := exit6 _ c₁ (by simp [hc₁])
        (by rw [hu₁.tapes (d := E) (by simp)]; exact hE) (by rw [hu₁.pos (d := E) (by simp)]; exact hpos)
        (by rw [hu₁.tapes (d := C) (by simp), hu₁.pos (d := C) (by simp)]; exact hC)
      refine ⟨_, by simp; omega, c', ((h.trans hr).cast_n rfl).cast_out (by simp), hs,
        (hu₁.trans hu).mono (by simp) (by simp), ?_, ?_, ?_, hEp', ?_⟩
      · rw [hC', hu₁.tapes (d := C) (by simp)]
      · rw [hCp', hu₁.pos (d := C) (by simp)]
      · rw [hE', hu₁.tapes (d := E) (by simp)]
      · rw [Env.get_nil', S_nil]
        refine ⟨?_, ?_, ?_⟩
        · rw [← hu₁.pos (d := X) (by simp)]; exact hde.holds
        · intro q hq'
          rw [hde.outside q (by rw [hu₁.pos (d := X) (by simp)]; exact hq'), hu₁.tapes (d := X) (by simp)]
        · rw [hde.pos, hu₁.pos (d := X) (by simp)]
    | cons v rest =>
      obtain ⟨l₀, hpre⟩ := hpre
      obtain ⟨hSv, hsep, hbefore⟩ := hE.suffix_cells v rest hpre
      have hposv : c.workTapePos E = (envRepr rest).length + (S v).length := by
        rw [hpos, envRepr_cons]; simp; ring
      have hread : c.workTapes E (c.workTapePos E) = some .sep := by rw [hposv]; exact hsep
      have hCread : c.workTapes C (c.workTapePos C) = some .zero := by simpa using hC.head
      have h := step_instr hq hins
      simp only [execInstr, workTapeSymbols_eq, hread, hCread, Act.mw_out, Act.base_out,
        Option.toList_none, Act.mw_next, Act.base_next, resolve_stay] at h
      set c₁ := applyAct (((Act.base (.stay p4)).mw C 1).mw E (-1)) (some ⟨k, pc, p4⟩) c with hc₁
      have hu₁ : Untouched c c₁ [] [C, E] :=
        untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
          have h1 : d ≠ C := fun e => hd (by simp [e])
          have h2 : d ≠ E := fun e => hd (by simp [e])
          simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2]⟩ _ _
      have hC₁ : c₁.workTapes C = c.workTapes C := by
        rw [hc₁, applyAct_workTapes_of_none _ _ _ C (by simp [Act.mw_works_of_ne _ hCE])]
      have hCp₁ : c₁.workTapePos C = c.workTapePos C + 1 := by simp [hc₁, Act.mw_works_of_ne _ hCE]
      have hE₁ : c₁.workTapes E = c.workTapes E := by
        rw [hc₁, applyAct_workTapes_of_none _ _ _ E (by simp [Act.mw_works_of_ne _ hCE.symm])]
      have hEp₁ : c₁.workTapePos E = (envRepr rest).length + (S v).length - 1 := by
        simp [hc₁, hposv]; ring
      -- to the start of `S v`
      obtain ⟨c₂, hr₂, hs₂, hu₂, hE₂, hEp₂⟩ := getEnv_scan4 hins (S v) (mem_S v) c₁ (by simp [hc₁])
        (by rw [hE₁, hEp₁]; convert hSv using 1; ring)
        (by rw [hE₁, hEp₁]; convert hbefore using 3 <;> ring)
      have hEp₂' : c₂.workTapePos E = (envRepr rest).length := by rw [hEp₂, hEp₁]; ring
      -- copy it
      obtain ⟨c₃, hr₃, hs₃, hu₃, hE₃, hEp₃, hde₃⟩ := getEnv_copy5 hins (S v) (mem_S v) c₂ hs₂
        (by rw [hE₂, hE₁, hEp₂']; exact hSv) (by rw [hE₂, hE₁, hEp₂']; exact hsep)
      have hEp₃' : c₃.workTapePos E = (envRepr rest).length + (S v).length := by rw [hEp₃, hEp₂']
      -- to the end
      have hE₃' : EnvTape (c₃.workTapes E) env := by rw [hE₃, hE₂, hE₁]; exact hE
      have hqle : (envRepr rest).length + (S v).length ≤ (envRepr env).length := by
        rw [hpre, envRepr_cons]; simp
      obtain ⟨hhold, hend⟩ := hE₃'.tail_cells _ hqle
      obtain ⟨c₄, hr₄, hs₄, hu₄, hE₄, hEp₄⟩ := getEnv_toEnd hins hpc p8 (Or.inl rfl) _ c₃ hs₃
        (by rw [hEp₃']; exact_mod_cast hhold) (by rw [hEp₃']; exact_mod_cast hend)
      have hlen : (envRepr env).length = (envRepr rest).length + v.size + 1 + l₀.length := by
        rw [hpre, envRepr_cons]; simp; omega
      refine ⟨_, ?_, c₄, (((h.trans hr₂).trans hr₃).trans hr₄).cast_out (by simp), hs₄,
        (((hu₁.trans hu₂).trans hu₃).trans hu₄).mono (by simp) (by simp), ?_, ?_, ?_, ?_, ?_⟩
      · simp only [List.length_drop, envRepr_cons, List.length_append, List.length_singleton, length_S]
        omega
      · rw [hu₄.tapes (d := C) (by decide), hu₃.tapes (d := C) (by decide),
          hu₂.tapes (d := C) (by decide), hC₁]
      · rw [hu₄.pos (d := C) (by decide), hu₃.pos (d := C) (by decide),
          hu₂.pos (d := C) (by decide), hCp₁]; simp
      · rw [hE₄, hE₃, hE₂, hE₁]
      · rw [hEp₄, hEp₃']; simp only [List.length_drop]; push_cast; omega
      · rw [Env.get_cons_zero]
        refine ⟨?_, ?_, ?_⟩
        · rw [hu₄.tapes (d := X) (by decide), ← hu₁.pos (d := X) (by decide),
            ← hu₂.pos (d := X) (by decide)]
          exact hde₃.holds
        · intro q hq'
          rw [hu₄.tapes (d := X) (by decide),
            hde₃.outside q (by rw [hu₂.pos (d := X) (by decide), hu₁.pos (d := X) (by decide)]; exact hq'),
            hu₂.tapes (d := X) (by decide), hu₁.tapes (d := X) (by decide)]
        · rw [hu₄.pos (d := X) (by decide), hde₃.pos, hu₂.pos (d := X) (by decide),
            hu₁.pos (d := X) (by decide)]
  | succ j ih =>
    intro env' c hq hE hpre hpos hC
    cases env' with
    | nil =>
      simp only [envRepr_nil, List.length_nil, Nat.cast_zero, zero_sub] at hpos
      have hread : c.workTapes E (c.workTapePos E) = none := by rw [hpos]; exact hE.before _ (by norm_num)
      have h := step_instr hq hins
      simp only [execInstr, workTapeSymbols_eq, hread, Act.base_out, Option.toList_none, Act.base_next,
        resolve_stay] at h
      set c₁ := applyAct (Act.base (.stay p6)) (some ⟨k, pc, p6⟩) c with hc₁
      have hu₁ : Untouched c c₁ [] [] := untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _
      obtain ⟨c', hr, hs, hu, hC', hCp', hE', hEp', hde⟩ := exit6 _ c₁ (by simp [hc₁])
        (by rw [hu₁.tapes (d := E) (by simp)]; exact hE) (by rw [hu₁.pos (d := E) (by simp)]; exact hpos)
        (by rw [hu₁.tapes (d := C) (by simp), hu₁.pos (d := C) (by simp)]; exact hC)
      refine ⟨_, by simp; omega, c', ((h.trans hr).cast_n rfl).cast_out (by simp), hs,
        (hu₁.trans hu).mono (by simp) (by simp), ?_, ?_, ?_, hEp', ?_⟩
      · rw [hC', hu₁.tapes (d := C) (by simp)]
      · rw [hCp', hu₁.pos (d := C) (by simp)]
      · rw [hE', hu₁.tapes (d := E) (by simp)]
      · rw [Env.get_nil', S_nil]
        refine ⟨?_, ?_, ?_⟩
        · rw [← hu₁.pos (d := X) (by simp)]; exact hde.holds
        · intro q hq'
          rw [hde.outside q (by rw [hu₁.pos (d := X) (by simp)]; exact hq'), hu₁.tapes (d := X) (by simp)]
        · rw [hde.pos, hu₁.pos (d := X) (by simp)]
    | cons v rest =>
      obtain ⟨l₀, hpre⟩ := hpre
      obtain ⟨hSv, hsep, hbefore⟩ := hE.suffix_cells v rest hpre
      have hposv : c.workTapePos E = (envRepr rest).length + (S v).length := by
        rw [hpos, envRepr_cons]; simp; ring
      have hread : c.workTapes E (c.workTapePos E) = some .sep := by rw [hposv]; exact hsep
      rw [S_ofNat_succ] at hC
      have hCread : c.workTapes C (c.workTapePos C) = some .one := hC.head
      -- the unit: `p1` then `p2`
      have h := step_instr hq hins
      simp only [execInstr, workTapeSymbols_eq, hread, hCread, Act.mw_out, Act.base_out,
        Option.toList_none, Act.mw_next, Act.base_next, resolve_stay] at h
      set c₁ := applyAct (((Act.base (.stay p2)).mw C 1).mw E (-1)) (some ⟨k, pc, p2⟩) c with hc₁
      have hu₁ : Untouched c c₁ [] [C, E] :=
        untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
          have h1 : d ≠ C := fun e => hd (by simp [e])
          have h2 : d ≠ E := fun e => hd (by simp [e])
          simp [Act.mw_works_of_ne _ h1, Act.mw_works_of_ne _ h2]⟩ _ _
      have hC₁ : c₁.workTapes C = c.workTapes C := by
        rw [hc₁, applyAct_workTapes_of_none _ _ _ C (by simp [Act.mw_works_of_ne _ hCE])]
      have hCp₁ : c₁.workTapePos C = c.workTapePos C + 1 := by simp [hc₁, Act.mw_works_of_ne _ hCE]
      have hE₁ : c₁.workTapes E = c.workTapes E := by
        rw [hc₁, applyAct_workTapes_of_none _ _ _ E (by simp [Act.mw_works_of_ne _ hCE.symm])]
      have hEp₁ : c₁.workTapePos E = (envRepr rest).length + (S v).length - 1 := by
        simp [hc₁, hposv]; ring
      have h2 := step_instr (c := c₁) (k := k) (pc := pc) (ph := p2) (by simp [hc₁]) hins
      simp only [execInstr, Act.mw_out, Act.base_out, Option.toList_none, Act.mw_next, Act.base_next,
        resolve_stay] at h2
      set c₂ := applyAct ((Act.base (.stay p3)).mw C 1) (some ⟨k, pc, p3⟩) c₁ with hc₂
      have hu₂ : Untouched c₁ c₂ [] [C] :=
        untouched_applyAct ⟨fun j _ => rfl, fun d hd => by
          have : d ≠ C := by simpa using hd
          simp [Act.mw_works_of_ne _ this]⟩ _ _
      have hC₂ : c₂.workTapes C = c.workTapes C := by
        rw [hc₂, applyAct_workTapes_of_none _ _ _ C (by simp), hC₁]
      have hCp₂ : c₂.workTapePos C = c.workTapePos C + 2 := by simp [hc₂, hCp₁]; ring
      have hE₂ : c₂.workTapes E = c.workTapes E := by rw [hu₂.tapes (d := E) (by decide), hE₁]
      have hEp₂ : c₂.workTapePos E = (envRepr rest).length + (S v).length - 1 := by
        rw [hu₂.pos (d := E) (by decide), hEp₁]
      -- over `S v` to the previous separator
      obtain ⟨c₃, hr₃, hs₃, hu₃, hE₃, hEp₃⟩ := getEnv_scan3 hins (S v) (mem_S v) c₂ (by simp [hc₂])
        (by rw [hE₂, hEp₂]; convert hSv using 1; ring)
      have hE₃' : c₃.workTapes E = c.workTapes E := by rw [hE₃, hE₂]
      have hEp₃' : c₃.workTapePos E = (envRepr rest).length - 1 := by rw [hEp₃, hEp₂]; ring
      have hC₃ : c₃.workTapes C = c.workTapes C := by rw [hu₃.tapes (d := C) (by decide), hC₂]
      have hCp₃ : c₃.workTapePos C = c.workTapePos C + 2 := by rw [hu₃.pos (d := C) (by decide), hCp₂]
      have hC₃' : Holds (c₃.workTapes C) (c₃.workTapePos C) (S (Data.ofNat j)) := by
        rw [hC₃, hCp₃]; convert hC.tail.tail using 1; ring
      have hlen : (envRepr env).length = (envRepr rest).length + v.size + 1 + l₀.length := by
        rw [hpre, envRepr_cons]; simp; omega
      -- the separator or the blank before the tape
      have h4 := step_instr (c := c₃) (k := k) (pc := pc) (ph := p3) hs₃ hins
      rcases hbefore with hb | hb
      · -- a separator: continue the walk at `p1`
        have hread₃ : c₃.workTapes E (c₃.workTapePos E) = some .sep := by rw [hE₃', hEp₃']; exact hb
        simp only [execInstr, workTapeSymbols_eq, hread₃, Act.base_out, Option.toList_none,
          Act.base_next, resolve_stay] at h4
        set c₄ := applyAct (Act.base (.stay p1)) (some ⟨k, pc, p1⟩) c₃ with hc₄
        have hu₄ : Untouched c₃ c₄ [] [] := untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _
        obtain ⟨n, hn, c', hr, hs, hu, hC', hCp', hE', hEp', hde⟩ := ih rest c₄ (by simp [hc₄])
          (by rw [hu₄.tapes (d := E) (by simp), hE₃']; exact hE)
          ⟨S v ++ [.sep] ++ l₀, by rw [hpre, envRepr_cons]; simp⟩
          (by rw [hu₄.pos (d := E) (by simp), hEp₃'])
          (by rw [hu₄.tapes (d := C) (by simp), hu₄.pos (d := C) (by simp)]; exact hC₃')
        refine ⟨1 + 1 + (S v).length + 1 + n, ?_, c', ?_, hs,
          ((((hu₁.trans hu₂).trans hu₃).trans hu₄).trans hu).mono (by simp) (by simp), ?_, ?_, ?_,
          hEp', ?_⟩
        · simp only [envRepr_cons, List.length_append, List.length_singleton] at hn ⊢; omega
        · exact ((((h.trans h2).trans hr₃).trans h4).trans hr).cast_out (by simp)
        · rw [hC', hu₄.tapes (d := C) (by simp), hC₃]
        · rw [hCp', hu₄.pos (d := C) (by simp), hCp₃]; push_cast; ring
        · rw [hE', hu₄.tapes (d := E) (by simp), hE₃']
        · rw [Env.get_cons_succ]
          have hXt : c₄.workTapes X = c.workTapes X := by
            rw [hu₄.tapes (d := X) (by simp), hu₃.tapes (d := X) (by decide),
              hu₂.tapes (d := X) (by decide), hu₁.tapes (d := X) (by decide)]
          have hXp : c₄.workTapePos X = c.workTapePos X := by
            rw [hu₄.pos (d := X) (by simp), hu₃.pos (d := X) (by decide),
              hu₂.pos (d := X) (by decide), hu₁.pos (d := X) (by decide)]
          refine ⟨?_, ?_, ?_⟩
          · rw [← hXp]; exact hde.holds
          · intro q hq'; rw [hde.outside q (by rw [hXp]; exact hq'), hXt]
          · rw [hde.pos, hXp]
      · -- the blank before the tape: out of range
        have hread₃ : c₃.workTapes E (c₃.workTapePos E) = none := by rw [hE₃', hEp₃']; exact hb
        simp only [execInstr, workTapeSymbols_eq, hread₃, Act.base_out, Option.toList_none,
          Act.base_next, resolve_stay] at h4
        set c₄ := applyAct (Act.base (.stay p6)) (some ⟨k, pc, p6⟩) c₃ with hc₄
        have hu₄ : Untouched c₃ c₄ [] [] := untouched_applyAct ⟨fun _ _ => rfl, fun _ _ => rfl⟩ _ _
        have hrest : rest = [] := by
          cases rest with
          | nil => rfl
          | cons w rest' =>
            exfalso
            have h6 : (envRepr (w :: rest')).length - 1 < (envRepr env).length := by
              rw [hpre]; simp only [envRepr_cons, List.length_append, List.length_singleton]; omega
            have h7 : 1 ≤ (envRepr (w :: rest')).length := by
              simp only [envRepr_cons, List.length_append, List.length_singleton]; omega
            have h8 := hE.holds ((envRepr (w :: rest')).length - 1) h6
            rw [zero_add, Nat.cast_sub h7, Nat.cast_one, hb] at h8
            exact absurd h8 (by simp)
        subst hrest
        obtain ⟨c', hr, hs, hu, hC', hCp', hE', hEp', hde⟩ := exit6 j c₄ (by simp [hc₄])
          (by rw [hu₄.tapes (d := E) (by simp), hE₃']; exact hE)
          (by rw [hu₄.pos (d := E) (by simp), hEp₃']; simp)
          (by rw [hu₄.tapes (d := C) (by simp), hu₄.pos (d := C) (by simp)]; exact hC₃')
        refine ⟨_, ?_, c', ((((h.trans h2).trans hr₃).trans h4).trans hr).cast_out (by simp), hs,
          ((((hu₁.trans hu₂).trans hu₃).trans hu₄).trans hu).mono (by simp) (by simp), ?_, ?_, ?_,
          hEp', ?_⟩
        · simp only [envRepr_cons, envRepr_nil, List.nil_append, List.length_append,
            List.length_singleton] at hlen ⊢
          omega
        · rw [hC', hu₄.tapes (d := C) (by simp), hC₃]
        · rw [hCp', hu₄.pos (d := C) (by simp), hCp₃]; push_cast; ring
        · rw [hE', hu₄.tapes (d := E) (by simp), hE₃']
        · rw [Env.get_cons_succ, Env.get_nil', S_nil]
          have hXt : c₄.workTapes X = c.workTapes X := by
            rw [hu₄.tapes (d := X) (by simp), hu₃.tapes (d := X) (by decide),
              hu₂.tapes (d := X) (by decide), hu₁.tapes (d := X) (by decide)]
          have hXp : c₄.workTapePos X = c.workTapePos X := by
            rw [hu₄.pos (d := X) (by simp), hu₃.pos (d := X) (by decide),
              hu₂.pos (d := X) (by decide), hu₁.pos (d := X) (by decide)]
          refine ⟨?_, ?_, ?_⟩
          · rw [← hXp]; exact hde.holds
          · intro q hq'; rw [hde.outside q (by rw [hXp]; exact hq'), hXt]
          · rw [hde.pos, hXp]
end MIPRE.TM.Interp
