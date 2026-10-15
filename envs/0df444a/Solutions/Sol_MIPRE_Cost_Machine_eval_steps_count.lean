-- Prove2me | solution 1 for MIPRE.Cost.Machine.eval_steps_count
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:38:43.733388+00:00
-- url     : https://prove2.me/submissions/1b4cf70f-a087-4d9e-8da3-7786bd211132

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/MachineBound.lean (solution of MIPRE.Cost.Machine.eval_steps_count);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
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
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Machine
import Definitions.Def_MIPRE_Foundations_Cost_Codable
import Definitions.Def_MIPRE_Foundations_Cost_MachineData
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context; each is used only by proofs. -/
namespace MIPRE.Cost.Machine
theorem costSum_add (c : Cfg) (m n : ℕ) :
    costSum c (m + n) = costSum c m + costSum (step^[m] c) n := by
  induction m generalizing c with
  | zero => simp [costSum]
  | succ m ih =>
    rw [show m + 1 + n = (m + n) + 1 by omega, costSum, ih (step c), costSum,
      Function.iterate_succ_apply]
    omega
end MIPRE.Cost.Machine

namespace MIPRE.Cost.Machine.Steps
theorem one (c : Cfg) : Steps c 1 (step c) (stepCost c) := ⟨rfl, by simp [costSum]⟩
end MIPRE.Cost.Machine.Steps

namespace MIPRE.Cost.Machine.Steps
theorem trans {c₁ c₂ c₃ : Cfg} {m n t₁ t₂ : ℕ} (h₁ : Steps c₁ m c₂ t₁) (h₂ : Steps c₂ n c₃ t₂) :
    Steps c₁ (m + n) c₃ (t₁ + t₂) := by
  obtain ⟨h₁, c₁'⟩ := h₁
  obtain ⟨h₂, c₂'⟩ := h₂
  refine ⟨?_, ?_⟩
  · rw [Nat.add_comm, Function.iterate_add_apply, h₁, h₂]
  · rw [costSum_add, h₁, c₁', c₂']
end MIPRE.Cost.Machine.Steps

namespace MIPRE.Cost.Machine.Steps
theorem cast {c c' : Cfg} {N t t' : ℕ} (h : Steps c N c' t) (e : t = t') : Steps c N c' t' :=
  e ▸ h
end MIPRE.Cost.Machine.Steps

namespace MIPRE.Cost.Machine.Steps
theorem of_succ {c c' : Cfg} {N t : ℕ} (h : Steps c (N + 1) c' t) :
    ∃ t', t = stepCost c + t' ∧ Steps (step c) N c' t' := by
  obtain ⟨h, hc⟩ := h
  refine ⟨costSum (step c) N, ?_, ?_, rfl⟩
  · rw [← hc, costSum]
  · rw [← h, Function.iterate_succ_apply]
end MIPRE.Cost.Machine.Steps

namespace MIPRE.Cost.Machine.Steps
theorem ne_zero {p : Prog} {env : Env} {k : List Frame} {N : ℕ} {r : Data} {e : Env} {t : ℕ}
    (h : Steps ⟨.ev p, env, k⟩ N ⟨.ret r, e, k⟩ t) : N ≠ 0 := by
  rintro rfl
  obtain ⟨h, -⟩ := h
  simp at h
end MIPRE.Cost.Machine.Steps

/-! The uploaded declaration, hoisted to the top level as `solution`. -/
open MIPRE
open MIPRE.Cost
open MIPRE.Cost.Machine
theorem solution {env : Env} {p : Prog} {r : Data} {t : ℕ} (h : Eval env p r t)
    (k : List Frame) :
    ∃ N env', Steps ⟨.ev p, env, k⟩ N ⟨.ret r, env', k⟩ t ∧ N ≤ 3 * t := by
  induction h generalizing k with
  | var env i => exact ⟨1, env, Steps.one _, by omega⟩
  | nil env => exact ⟨1, env, Steps.one _, by omega⟩
  | const env d => exact ⟨1, env, Steps.one _, by have := Data.size_pos d; omega⟩
  | cons h₁ h₂ ih₁ ih₂ =>
    rename_i env h t a b s u
    obtain ⟨N₁, e₁, h₁, hN₁⟩ := ih₁ (.cons1 t env :: k)
    obtain ⟨N₂, e₂, h₂, hN₂⟩ := ih₂ (.cons2 a :: k)
    have := (((Steps.one ⟨.ev (.cons h t), env, k⟩).trans h₁).trans
      ((Steps.one ⟨.ret a, e₁, .cons1 t env :: k⟩).trans h₂)).trans
      (Steps.one ⟨.ret b, e₂, .cons2 a :: k⟩)
    exact ⟨_, e₂, this.cast (by simp [stepCost]; omega), by omega⟩
  | elim_nil hget h₁ ih =>
    rename_i env i n c r t
    obtain ⟨N, e, h, hN⟩ := ih k
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev n, env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    exact ⟨_, e, (h0.trans h).cast (by omega), by omega⟩
  | elim_cons hget h₁ ih =>
    rename_i env i n c a b r t
    obtain ⟨N, e, h, hN⟩ := ih k
    have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev c, a :: b :: env, k⟩ 1 := by
      have := Steps.one ⟨.ev (.elim i n c), env, k⟩
      simp only [step, stepCost, hget] at this
      exact this
    exact ⟨_, e, (h0.trans h).cast (by omega), by omega⟩
  | let_ h₁ h₂ ih₁ ih₂ =>
    rename_i env e b v r s t
    obtain ⟨N₁, e₁, h₁, hN₁⟩ := ih₁ (.let1 b env :: k)
    obtain ⟨N₂, e₂, h₂, hN₂⟩ := ih₂ k
    have := (((Steps.one ⟨.ev (.let_ e b), env, k⟩).trans h₁).trans
      (Steps.one ⟨.ret v, e₁, .let1 b env :: k⟩)).trans h₂
    exact ⟨_, e₂, this.cast (by simp [stepCost]; omega), by omega⟩
  | loop_nil h₁ ih =>
    rename_i env b t
    obtain ⟨N, e, h, hN⟩ := ih (.loop1 b env :: k)
    have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans h).trans
      (Steps.one ⟨.ret .nil, e, .loop1 b env :: k⟩)
    exact ⟨_, env, this.cast (by simp [stepCost]), by omega⟩
  | loop_stop h₁ ih =>
    rename_i env b r t
    obtain ⟨N, e, h, hN⟩ := ih (.loop1 b env :: k)
    have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans h).trans
      (Steps.one ⟨.ret (.cons .nil r), e, .loop1 b env :: k⟩)
    exact ⟨_, env, this.cast (by simp [stepCost]), by omega⟩
  | loop_step h₁ h₂ ih₁ ih₂ =>
    rename_i env b x y v r s t
    obtain ⟨N₁, e₁, h₁, hN₁⟩ := ih₁ (.loop1 b env :: k)
    obtain ⟨N₂, e₂, h₂, hN₂⟩ := ih₂ k
    obtain ⟨N₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero h₂.ne_zero
    obtain ⟨t₂, ht₂, h₂'⟩ := h₂.of_succ
    have := (((Steps.one ⟨.ev (.loop b), env, k⟩).trans h₁).trans
      (Steps.one ⟨.ret (.cons (.cons x y) v), e₁, .loop1 b env :: k⟩)).trans h₂'
    exact ⟨_, e₂, this.cast (by simp only [stepCost] at ht₂ ⊢; omega), by omega⟩
