-- Prove2me | solution 1 for MIPRE.TM.Interp.accepts_of_acceptsWithin
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:11:36.269605+00:00
-- url     : https://prove2.me/submissions/4b2dfa26-04bd-4db8-a01c-a8f68153af22

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/TM/Interp/Run.lean (solution of MIPRE.TM.Interp.accepts_of_acceptsWithin);
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
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_bound
import Theorems.Thm_MIPRE_Cost_Machine_eval_steps_count
import Theorems.Thm_MIPRE_TM_Interp_final_run
import Theorems.Thm_MIPRE_TM_Interp_init_run
import Theorems.Thm_MIPRE_TM_Interp_length_frameRepr_le
import Theorems.Thm_MIPRE_TM_Interp_sim_run

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
open MIPRE.Cost MIPRE.Cost.Machine
theorem length_envRepr (env : Env) :
    (envRepr env).length = (env.map Data.size).sum + env.length := by
  induction env with
  | nil => simp
  | cons v env ih => simp [ih]; omega
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
theorem length_envRepr_le {V L : ℕ} (env : Env) (hL : env.length ≤ L) (hV : ∀ v ∈ env, v.size ≤ V) :
    (envRepr env).length ≤ L * V + L := by
  rw [length_envRepr]
  have hsum : (env.map Data.size).sum ≤ L * V := by
    calc (env.map Data.size).sum ≤ (env.map fun _ => V).sum := List.sum_le_sum (fun v hv => hV v hv)
      _ = env.length * V := by simp [List.map_const', List.sum_replicate]
      _ ≤ L * V := Nat.mul_le_mul_right V hL
  omega
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
theorem length_kontRepr_le {V L P K : ℕ} (k : List Frame) (hK : k.length ≤ K)
    (hf : ∀ f ∈ k, FrameBound V L P f) :
    (kontRepr k).length ≤ K * (V + P + L * V + L + 4) := by
  induction k generalizing K with
  | nil => simp
  | cons f k ih =>
    simp only [List.length_cons] at hK
    have := ih (K := K - 1) (by omega) (fun f' hf' => hf f' (List.mem_cons_of_mem _ hf'))
    have hfr := length_frameRepr_le (hf f List.mem_cons_self)
    rw [kontRepr_cons, List.length_append]
    calc (kontRepr k).length + (frameRepr f).length
        ≤ (K - 1) * (V + P + L * V + L + 4) + (V + P + L * V + L + 4) := by omega
      _ = (K - 1 + 1) * (V + P + L * V + L + 4) := by ring
      _ ≤ K * (V + P + L * V + L + 4) := Nat.mul_le_mul_right _ (by omega)
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
theorem sz_le {V L P K : ℕ} {m : Machine.Cfg} (h : CfgBound V L P K m) : sz m ≤ szBound V L P K := by
  have hc : (ctrlRepr m.ctrl).length ≤ V + P + 2 := by
    cases hm : m.ctrl with
    | ev p =>
      have := h.ctrl_prog p hm
      rw [Prog.esize_eq_size_toData] at this
      simp [ctrlRepr]; omega
    | ret v =>
      have := h.ctrl_val v hm
      simp [ctrlRepr]; omega
  have he := length_envRepr_le m.env h.env_len h.env_val
  have hk := length_kontRepr_le m.kont h.kont_len h.frames
  simp only [sz, szBound]
  omega
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
theorem cfgBound_init (D : Prog) (n : ℕ) (x y a b : BitStr) (Tb : ℕ) :
    CfgBound (V0 n x y a b Tb) 1 (esize D) 0 ⟨.ev D, [encode (n, x, y, a, b)], []⟩ where
  ctrl_val v hv := by simp at hv
  ctrl_prog p hp := by simp only [Ctrl.ev.injEq] at hp; subst hp; exact le_rfl
  env_len := by simp
  env_val v hv := by simp at hv; subst hv; exact le_max_left _ _
  kont_len := by simp
  frames f hf := by simp at hf
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
    (ha : a.length ≤ Tb) (hb : b.length ≤ Tb) (h : D.AcceptsWithin n x y a b Tb) :
    ∃ m ≤ runBound D.prog n x y a b Tb, AcceptsFrom (U.initCfg (uInput D.prog n Tb x y a b)) m := by
  classical
  obtain ⟨t, ht, hev⟩ := h
  set v := encode (n, x, y, a, b) with hv
  set m₀ : Machine.Cfg := ⟨.ev D.prog, [v], []⟩ with hm₀
  obtain ⟨N, e, hsteps, hN⟩ := eval_steps_count hev []
  obtain ⟨N', e', hsteps', hbnd⟩ := eval_steps_bound hev [] (V0 n x y a b Tb) 1 (esize D.prog) 0
    (cfgBound_init D.prog n x y a b Tb) (le_max_of_le_right ht)
  -- the first final configuration
  have hex : ∃ i, IsFinal (Machine.step^[i] m₀) := ⟨N, hsteps.1 ▸ ⟨_, _, rfl⟩⟩
  obtain ⟨N₀, hfin, hmin, hN₀N, hN₀N'⟩ : ∃ N₀, IsFinal (Machine.step^[N₀] m₀) ∧
      (∀ i < N₀, ¬ IsFinal (Machine.step^[i] m₀)) ∧ N₀ ≤ N ∧ N₀ ≤ N' :=
    ⟨Nat.find hex, Nat.find_spec hex, fun i hi => Nat.find_min hex hi,
      Nat.find_min' hex (hsteps.1 ▸ ⟨_, _, rfl⟩), Nat.find_min' hex (hsteps'.1 ▸ ⟨_, _, rfl⟩)⟩
  obtain ⟨r₀, e₀, hfin'⟩ := hfin
  -- the final value is `encode true`
  have hr₀ : r₀ = encode true := by
    have := hsteps.1
    rw [show N = N₀ + (N - N₀) by omega, Nat.add_comm, Function.iterate_add_apply, hfin',
      step_fixed_of_final] at this
    exact Ctrl.ret.inj (Machine.Cfg.mk.inj this).1
  -- the cost up to `N₀`
  have hcost : costSum m₀ N₀ ≤ Tb := (costSum_mono m₀ hN₀N).trans (hsteps.2 ▸ ht)
  -- the sizes along the run
  have hZ : ∀ i < N₀, sz (Machine.step^[i] m₀) ≤ Z0 D.prog n x y a b Tb := fun i hi =>
    sz_le ((hbnd i (by omega)).mono le_rfl (by omega) le_rfl (by omega))
  have hnf : ∀ i < N₀, ∀ w, (Machine.step^[i] m₀).ctrl = .ret w → (Machine.step^[i] m₀).kont ≠ [] := by
    intro i hi w hw hk
    exact hmin i hi ⟨w, (Machine.step^[i] m₀).env, by
      rcases hc : Machine.step^[i] m₀ with ⟨ctrl, env, kont⟩
      simp only [hc] at hw hk
      subst hw hk; rfl⟩
  -- the run of `U`
  obtain ⟨m₁, hm₁, c₁, ds₁, hr₁, hd₁, hrep₁, hx₁⟩ := init_run D.prog n x y a b Tb ha hb
  obtain ⟨n₂, hN₂, hn₂, c₂, ds₂, hr₂, hd₂, hrep₂, hx₂⟩ :=
    sim_run (Z0 D.prog n x y a b Tb) N₀ m₀ c₁ ds₁ Tb hd₁ hrep₁ hZ hnf hcost
  rw [hfin'] at hrep₂
  obtain ⟨n₃, hn₃, hacc⟩ := (final_run hd₂ hrep₂).1 (by rw [hr₀]; rfl)
  have hr₀V : r₀.size ≤ V0 n x y a b Tb := by
    have := (hbnd N₀ hN₀N').ctrl_val r₀ (by rw [hfin'])
    exact this
  refine ⟨m₁ + n₂ + n₃, ?_, ?_⟩
  · have hZ0 : 1 ≤ Z0 D.prog n x y a b Tb := by simp [szBound]
    have hn₂' : n₂ ≤ 3 * Tb * stepB (Z0 D.prog n x y a b Tb) (3 * Tb * Z0 D.prog n x y a b Tb) := by
      refine hn₂.trans ?_
      have hN₀T : N₀ ≤ 3 * Tb := by omega
      refine Nat.mul_le_mul hN₀T ?_
      simp only [stepB]
      have : (ds₁ X).l.length + N₀ * Z0 D.prog n x y a b Tb ≤ 3 * Tb * Z0 D.prog n x y a b Tb := by
        rw [hx₁]; nlinarith
      omega
    simp only [runBound]; omega
  · obtain ⟨c₃, hr₃, hs₃⟩ := hacc
    exact ⟨c₃, ((hr₁.trans hr₂).trans hr₃).cast_out (by simp), hs₃⟩
end MIPRE.TM.Interp
