-- Prove2me | solution 1 for MIPRE.TM.Interp.acceptsWithin_of_accepts
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:11:49.170796+00:00
-- url     : https://prove2.me/submissions/13a87832-6e6d-46c3-a793-f74610769d2f

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Run.lean (solution of MIPRE.TM.Interp.acceptsWithin_of_accepts);
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
import Theorems.Thm_MIPRE_Cost_Machine_eval_of_steps
import Theorems.Thm_MIPRE_TM_Interp_final_run
import Theorems.Thm_MIPRE_TM_Interp_init_run
import Theorems.Thm_MIPRE_TM_Interp_sim_run
import Theorems.Thm_MIPRE_TM_Interp_step_fail

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
/-- From a halting configuration, a machine does not output anything. -/
lemma outputString_halt
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input)
    (h_halt : cfg.state = none)
    (t : ℕ) :
    tm.outputString cfg t = [] := by
  induction t with
  | zero => simp [outputString]
  | succ t ih => simp [outputString_succ, ih, h_halt]
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

namespace Turing.MultiInputTM
section
open Relation
open MultiTapeTM (moveInputPos)
open Cfg
variable {i w : ℕ} {State Symbol : Type*}
variable {tm : MultiInputTM i w Symbol State}
variable {input : Fin i → List Symbol}
/-- The output does not change after the machine has halted. -/
lemma outputString_eq_of_halt
    (tm : MultiInputTM i w Symbol State)
    (cfg : Cfg i w Symbol State input) {τ t : ℕ} (hle : τ ≤ t)
    (hhalt : (tm.configs cfg τ).state = none) :
    tm.outputString cfg t = tm.outputString cfg τ := by
  conv_lhs => rw [← Nat.sub_add_cancel hle, Nat.add_comm]
  rw [outputString_add_eq_append, outputString_halt _ _ hhalt]
  simp
end
end Turing.MultiInputTM

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
open Turing MultiInputTM
open MultiTapeTM (moveInputPos)
variable {input : Fin 7 → List Sym}
/-- A silent run followed by a silent halt. -/
theorem HaltsIn.after {c c' : Cfg input} {n m : ℕ} (h : Reach c n c' []) (h' : HaltsIn c' m) :
    HaltsIn c (n + m) := by
  unfold HaltsIn at *
  rw [configs_add, outputString_add_eq_append, h.1, h.2, h'.2]
  exact ⟨h'.1, rfl⟩
end
end MIPRE.TM.Interp

namespace MIPRE.TM.Interp.Desc
section
open Turing MultiInputTM Phase MIPRE.Cost
variable {input : Fin 7 → List Sym}
variable {c : Cfg input} {q : Option Ctl} {ds : WT → TapeSt}
theorem state (h : Desc c q ds) : c.state = q := h.1
end
end MIPRE.TM.Interp.Desc

namespace MIPRE.TM.Interp
section
open Turing MultiInputTM Phase MIPRE.Cost MIPRE.Cost.Machine
open MultiTapeTM (moveInputPos)
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
set_option linter.unnecessarySimpa false
variable {input : Fin 7 → List Sym}
theorem costSum_succ (m : Machine.Cfg) (N : ℕ) :
    costSum m (N + 1) = costSum m N + stepCost (Machine.step^[N] m) := by
  rw [costSum_add]; simp [costSum]
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
theorem costSum_mono (m : Machine.Cfg) {a b : ℕ} (h : a ≤ b) : costSum m a ≤ costSum m b := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [costSum_add]; omega
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
theorem no_accept_of_haltsIn {c : Cfg input} {n : ℕ} (h : HaltsIn c n) (S : ℕ) :
    U.outputString c S ≠ [.one] := by
  rcases Nat.lt_or_ge S n with hS | hS
  · intro hout
    have := outputString_add_eq_append U c S (n - S)
    rw [Nat.add_sub_cancel' hS.le, h.2, hout] at this
    simp at this
  · rw [outputString_eq_of_halt U c hS h.1, h.2]
    simp
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
/-- Final configurations are fixed by `step`. -/
theorem step_fixed_of_final {r : Data} {e : Env} (n : ℕ) :
    Machine.step^[n] (⟨.ret r, e, []⟩ : Machine.Cfg) = ⟨.ret r, e, []⟩ :=
  Function.iterate_fixed rfl n
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
theorem _root_.solution (D : Decider) (n : ℕ) (x y a b : BitStr) (Tb : ℕ)
    (ha : a.length ≤ Tb) (hb : b.length ≤ Tb) (S : ℕ)
    (hS : (U.configs (U.initCfg (uInput D.prog n Tb x y a b)) S).state = none ∧
      U.outputString (U.initCfg (uInput D.prog n Tb x y a b)) S = [.one]) :
    D.AcceptsWithin n x y a b Tb := by
  classical
  set v := encode (n, x, y, a, b) with hv
  set m₀ : Machine.Cfg := ⟨.ev D.prog, [v], []⟩ with hm₀
  set c₀ := U.initCfg (uInput D.prog n Tb x y a b) with hc₀
  obtain ⟨m₁, hm₁, c₁, ds₁, hr₁, hd₁, hrep₁, hx₁⟩ := init_run D.prog n x y a b Tb ha hb
  -- the first step that is final, over budget, or the `S`-th
  have hex : ∃ i, IsFinal (Machine.step^[i] m₀) ∨ Tb < costSum m₀ (i + 1) ∨ S ≤ i :=
    ⟨S, Or.inr (Or.inr le_rfl)⟩
  obtain ⟨N, hspec, hmin'⟩ : ∃ N, (IsFinal (Machine.step^[N] m₀) ∨ Tb < costSum m₀ (N + 1) ∨ S ≤ N) ∧
      ∀ i < N, ¬ (IsFinal (Machine.step^[i] m₀) ∨ Tb < costSum m₀ (i + 1) ∨ S ≤ i) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi⟩
  have hmin : ∀ i < N, ¬ IsFinal (Machine.step^[i] m₀) ∧ costSum m₀ (i + 1) ≤ Tb ∧ i < S := by
    intro i hi
    have := hmin' i hi
    push Not at this
    exact this
  have hcost : costSum m₀ N ≤ Tb := by
    rcases Nat.eq_zero_or_pos N with h0 | hpos
    · rw [h0]; simp [costSum]
    · have := (hmin (N - 1) (by omega)).2.1
      rwa [Nat.sub_add_cancel hpos] at this
  have hnf : ∀ i < N, ∀ w, (Machine.step^[i] m₀).ctrl = .ret w → (Machine.step^[i] m₀).kont ≠ [] := by
    intro i hi w hw hk
    exact (hmin i hi).1 ⟨w, (Machine.step^[i] m₀).env, by
      rcases hc : Machine.step^[i] m₀ with ⟨ctrl, env, kont⟩
      simp only [hc] at hw hk
      subst hw hk; rfl⟩
  -- a size bound along these steps
  set Z := ((List.range N).map fun i => sz (Machine.step^[i] m₀)).sum with hZdef
  have hZ : ∀ i < N, sz (Machine.step^[i] m₀) ≤ Z := fun i hi =>
    List.le_sum_of_mem (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)
  obtain ⟨n₂, hN₂, hn₂, c₂, ds₂, hr₂, hd₂, hrep₂, hx₂⟩ :=
    sim_run Z N m₀ c₁ ds₁ Tb hd₁ hrep₁ hZ hnf hcost
  have hR : Reach c₀ (m₁ + n₂) c₂ [] := (hr₁.trans hr₂).cast_out (by simp)
  -- no silent halt is compatible with acceptance
  have hno : ∀ k, ¬ HaltsIn c₂ k := fun k hk =>
    no_accept_of_haltsIn (HaltsIn.after hR hk) S hS.2
  rcases hspec with hfin | hover | hSN
  · -- final: the value must be `encode true`, and the derivation has cost at most `T`
    obtain ⟨r₀, e₀, hfin'⟩ := hfin
    rw [hfin'] at hrep₂
    by_cases hr₀ : r₀ = Data.ofBool true
    · obtain ⟨r', t, M, e', N', hNM, hev, hst⟩ := eval_of_steps N D.prog [v] [] r₀ e₀ hfin'
      have hr' : r' = r₀ := by
        have := hfin'
        rw [hNM, Nat.add_comm, Function.iterate_add_apply, hst.1, step_fixed_of_final] at this
        exact (Ctrl.ret.inj (Machine.Cfg.mk.inj this).1)
      refine ⟨t, ?_, ?_⟩
      · have := costSum_mono m₀ (show M ≤ N by omega)
        rw [hst.2] at this
        exact this.trans hcost
      · rw [hr', hr₀] at hev
        exact hev
    · exact absurd ((final_run hd₂ hrep₂).2 hr₀) (hno _)
  · -- over budget: `U` halts silently
    exfalso
    have hnf' : ∀ w, (Machine.step^[N] m₀).ctrl = .ret w → (Machine.step^[N] m₀).kont ≠ [] := by
      intro w hw hk
      apply hno 0
      exfalso
      -- a final configuration is fixed and costs nothing; then the budget is not exceeded
      have hfin : IsFinal (Machine.step^[N] m₀) := ⟨w, (Machine.step^[N] m₀).env, by
        rcases hc : Machine.step^[N] m₀ with ⟨ctrl, env, kont⟩
        simp only [hc] at hw hk
        subst hw hk; rfl⟩
      obtain ⟨r₀, e₀, hfin'⟩ := hfin
      rw [costSum_succ, hfin'] at hover
      simp [stepCost] at hover
      omega
    rw [costSum_succ] at hover
    exact hno _ (step_fail hd₂ hrep₂ hnf' (by omega))
  · -- the `S`-th step: `U` is still running at time `S`
    exfalso
    have hstate : (U.configs c₀ (m₁ + n₂)).state ≠ none := by
      rw [hR.1, hd₂.state]; simp
    apply hstate
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show S ≤ m₁ + n₂ by omega)
    rw [hd, configs_add, configs_of_halts _ hS.1]
    exact hS.1
end MIPRE.TM.Interp
