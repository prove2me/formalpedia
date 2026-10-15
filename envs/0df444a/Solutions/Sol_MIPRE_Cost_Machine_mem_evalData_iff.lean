-- Prove2me | solution 1 for MIPRE.Cost.Machine.mem_evalData_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T17:42:14.081861+00:00
-- url     : https://prove2.me/submissions/68ee62aa-4102-4542-87a1-87f4c4195d0d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Partrec.lean (solution of MIPRE.Cost.Machine.mem_evalData_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Computability.Partrec
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_Partrec
import Theorems.Thm_MIPRE_Cost_Machine_halts_iff
import Theorems.Thm_MIPRE_Cost_Machine_stepData_toData

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Machine
theorem initData_eq (p : Prog) (x : Data) : initData p.toData x = Cfg.toData ⟨.ev p, [x], []⟩ :=
  rfl
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem isFinalD_toData (c : Cfg) : IsFinalD c.toData ↔ ∃ r e, c = ⟨.ret r, e, []⟩ := by
  obtain ⟨ctrl, env, kont⟩ := c
  cases ctrl with
  | ev p =>
    simp [IsFinalD, Cfg.toData, Ctrl.toData, evD]
  | ret v =>
    cases kont with
    | nil => simp [IsFinalD, Cfg.toData, Ctrl.toData, retD]
    | cons f k => simp [IsFinalD, Cfg.toData, Ctrl.toData, retD]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem resultD_toData (r : Data) (e : Env) : resultD (Cfg.toData ⟨.ret r, e, []⟩) = r := rfl
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
theorem iterate_stepData_toData (c : Cfg) (N : ℕ) :
    stepData^[N] c.toData = (step^[N] c).toData := by
  induction N generalizing c with
  | zero => rfl
  | succ N ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepData_toData, ih]
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem exists_iterate_of_mem_fix {d r : Data}
    (h : r ∈ PFun.fix (fun d => Part.some (evalStep d)) d) :
    ∃ N, IsFinalD (stepData^[N] d) ∧ resultD (stepData^[N] d) = r := by
  refine PFun.fixInduction (C := fun d => ∃ N, IsFinalD (stepData^[N] d) ∧
    resultD (stepData^[N] d) = r) h fun d hd ih => ?_
  by_cases hf : IsFinalD d
  · refine ⟨0, hf, ?_⟩
    rcases PFun.mem_fix_iff.1 hd with h1 | ⟨d', hd', -⟩
    · simp [evalStep, hf] at h1
      exact h1.symm
    · simp [evalStep, hf] at hd'
  · rcases PFun.mem_fix_iff.1 hd with h1 | ⟨d', hd', -⟩
    · simp [evalStep, hf] at h1
    · have hd'' : d' = stepData d := by simpa [evalStep, hf] using hd'
      subst hd''
      obtain ⟨N, hN, hr⟩ := ih _ hd'
      exact ⟨N + 1, by rwa [Function.iterate_succ_apply], by rwa [Function.iterate_succ_apply]⟩
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine
open Primrec
theorem mem_fix_of_steps : ∀ (N : ℕ) (c : Cfg) (r : Data) (e : Env),
    step^[N] c = ⟨.ret r, e, []⟩ → r ∈ PFun.fix (fun d => Part.some (evalStep d)) c.toData := by
  intro N
  induction N with
  | zero =>
    intro c r e h
    simp only [Function.iterate_zero, id] at h
    subst h
    refine PFun.mem_fix_iff.2 (Or.inl ?_)
    have hf : IsFinalD (Cfg.toData ⟨.ret r, e, []⟩) := (isFinalD_toData _).2 ⟨r, e, rfl⟩
    simp [evalStep, hf, resultD_toData]
  | succ N ih =>
    intro c r e h
    by_cases hf : ∃ r' e', c = ⟨.ret r', e', []⟩
    · obtain ⟨r', e', rfl⟩ := hf
      have hfix := Function.iterate_fixed (f := step) (x := ⟨.ret r', e', []⟩) rfl (N + 1)
      rw [hfix] at h
      obtain rfl := Ctrl.ret.inj (Cfg.mk.inj h).1
      refine PFun.mem_fix_iff.2 (Or.inl ?_)
      have hf : IsFinalD (Cfg.toData ⟨.ret r', e', []⟩) := (isFinalD_toData _).2 ⟨r', e', rfl⟩
      simp [evalStep, hf, resultD_toData]
    · have hnf : ¬ IsFinalD c.toData := fun h' => hf ((isFinalD_toData c).1 h')
      refine PFun.mem_fix_iff.2 (Or.inr ⟨(step c).toData, ?_, ?_⟩)
      · simp [evalStep, hnf, stepData_toData]
      · rw [Function.iterate_succ_apply] at h
        exact ih (step c) r e h
end MIPRE.Cost.Machine

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
open Primrec
theorem solution (c : Prog) (x r : Data) :
    r ∈ evalData c.toData x ↔ ∃ t, c.Runs x r t := by
  rw [halts_iff, evalData, initData_eq]
  constructor
  · intro h
    obtain ⟨N, hN, hr⟩ := exists_iterate_of_mem_fix h
    rw [iterate_stepData_toData, isFinalD_toData] at hN
    obtain ⟨r', e, hc⟩ := hN
    rw [iterate_stepData_toData, hc, resultD_toData] at hr
    subst hr
    exact ⟨N, e, hc⟩
  · rintro ⟨N, e, hN⟩
    exact mem_fix_of_steps N _ r e hN
