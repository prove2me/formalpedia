-- Prove2me | solution 1 for MIPRE.TM.Interp.sim_run
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:10:04.889735+00:00
-- url     : https://prove2.me/submissions/04d0b217-b5c9-4473-b2e2-506bd61cdd10

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Run.lean (solution of MIPRE.TM.Interp.sim_run);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Language
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Sign.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation
import Mathlib.Tactic
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_SAT_Circuit
import Definitions.Def_MIPRE_Foundations_SAT_Cnf
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_CL_Closure_B
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_SAT_Succinct
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
import Definitions.Def_MIPRE_TM_Interp_InputRoutines
import Definitions.Def_MIPRE_TM_Interp_Run
import Theorems.Thm_MIPRE_TM_Interp_step_run

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

namespace MIPRE.TM.Interp.Reach
section
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
theorem refl (c : Cfg input) : Reach c 0 c [] := ⟨configs_zero, by simp [outputString]⟩
end
end MIPRE.TM.Interp.Reach

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
theorem cast_out {c c' : Cfg input} {n : ℕ} {out out' : List Sym} (h : Reach c n c' out)
    (e : out = out') : Reach c n c' out' := e ▸ h
end
end MIPRE.TM.Interp.Reach

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem stepBound_le {m : Machine.Cfg} {Z xl xl' : ℕ} (hZ : sz m ≤ Z) (hx : xl ≤ xl') :
    stepBound m xl ≤ stepB Z xl' := by
  simp only [stepBound, caseBound, stepB]; omega
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem stepB_mono (Z : ℕ) {xl xl' : ℕ} (hx : xl ≤ xl') : stepB Z xl ≤ stepB Z xl' := by
  simp only [stepB]; omega
end
end MIPRE.TM.Interp

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.TM.Interp
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem _root_.solution (Z : ℕ) : ∀ (N : ℕ) (m : Machine.Cfg) (c : Cfg input) (ds : WT → TapeSt) (r : ℕ),
    Desc c (at_ .dispatch 0) ds → RepOf ds m r (ctrlRepr m.ctrl).length (kontRepr m.kont).length →
    (∀ i < N, sz (Machine.step^[i] m) ≤ Z) →
    (∀ i < N, ∀ v, (Machine.step^[i] m).ctrl = .ret v → (Machine.step^[i] m).kont ≠ []) →
    costSum m N ≤ r →
    ∃ n, N ≤ n ∧ n ≤ N * stepB Z ((ds X).l.length + N * Z) ∧ ∃ (c' : Cfg input) (ds' : WT → TapeSt),
      Reach c n c' [] ∧ Desc c' (at_ .dispatch 0) ds' ∧
      RepOf ds' (Machine.step^[N] m) (r - costSum m N) (ctrlRepr (Machine.step^[N] m).ctrl).length
        (kontRepr (Machine.step^[N] m).kont).length ∧
      (ds' X).l.length ≤ (ds X).l.length + N * Z := by
  intro N
  induction N with
  | zero =>
    intro m c ds r hd hr _ _ _
    exact ⟨0, le_rfl, by simp, c, ds, Reach.refl c, hd, by simpa [costSum] using hr, by simp⟩
  | succ N ih =>
    intro m c ds r hd hr hZ hnf hcost
    have hZ0 := hZ 0 (by omega)
    simp only [Function.iterate_zero, id_eq] at hZ0
    have hsucc : costSum m (N + 1) = stepCost m + costSum (Machine.step m) N := rfl
    have hc1 : stepCost m ≤ r := by omega
    obtain ⟨n₁, h1, hn₁, c₁, ds₁, hr₁, hd₁, hrep₁, hxl₁⟩ :=
      step_run hd hr (hnf 0 (by omega)) hc1
    obtain ⟨n₂, hN₂, hn₂, c₂, ds₂, hr₂, hd₂, hrep₂, hxl₂⟩ := ih (Machine.step m) c₁ ds₁
      (r - stepCost m) hd₁ hrep₁
      (fun i hi => by simpa [Function.iterate_succ_apply] using hZ (i + 1) (by omega))
      (fun i hi => by simpa [Function.iterate_succ_apply] using hnf (i + 1) (by omega))
      (by omega)
    refine ⟨n₁ + n₂, by omega, ?_, c₂, ds₂, (hr₁.trans hr₂).cast_out (by simp), hd₂, ?_, ?_⟩
    · have hxb : (ds₁ X).l.length + N * Z ≤ (ds X).l.length + (N + 1) * Z := by
        rw [Nat.succ_mul]; omega
      have hb₁ : n₁ ≤ stepB Z ((ds X).l.length + (N + 1) * Z) :=
        hn₁.trans (stepBound_le hZ0 (by rw [Nat.succ_mul]; omega))
      have hb₂ : n₂ ≤ N * stepB Z ((ds X).l.length + (N + 1) * Z) :=
        hn₂.trans (Nat.mul_le_mul_left _ (stepB_mono Z hxb))
      calc n₁ + n₂ ≤ stepB Z ((ds X).l.length + (N + 1) * Z) +
            N * stepB Z ((ds X).l.length + (N + 1) * Z) := by omega
        _ = (N + 1) * stepB Z ((ds X).l.length + (N + 1) * Z) := by ring
    · rw [Function.iterate_succ_apply, hsucc, ← Nat.sub_sub]
      exact hrep₂
    · rw [Nat.succ_mul]; omega
end MIPRE.TM.Interp
