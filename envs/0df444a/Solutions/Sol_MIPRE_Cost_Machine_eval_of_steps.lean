-- Prove2me | solution 1 for MIPRE.Cost.Machine.eval_of_steps
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-12T16:36:49.794305+00:00
-- url     : https://prove2.me/submissions/cbc55efe-dfa5-40f1-b63b-57f075906ec4

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Cost/Machine.lean (solution of MIPRE.Cost.Machine.eval_of_steps);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Logic.Function.Iterate
import Definitions.Def_MIPRE_Foundations_Cost_Basic
import Definitions.Def_MIPRE_Foundations_Cost_Encoding
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_Cost_Machine

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
theorem solution : ∀ (N : ℕ) (p : Prog) (env : Env) (k : List Frame) (r : Data) (e : Env),
    step^[N] ⟨.ev p, env, k⟩ = ⟨.ret r, e, []⟩ →
    ∃ r' t M e' N', N = M + N' ∧ Eval env p r' t ∧ Steps ⟨.ev p, env, k⟩ M ⟨.ret r', e', k⟩ t := by
  intro N
  induction N using Nat.strongRecOn with
  | ind N ih =>
  intro p env k r e hN
  -- one step is always taken
  obtain ⟨N₀, rfl⟩ : ∃ N₀, N = N₀ + 1 := by
    cases N with
    | zero => simp at hN
    | succ N₀ => exact ⟨N₀, rfl⟩
  rw [Function.iterate_succ_apply] at hN
  cases p with
  | var i =>
    exact ⟨env.get i, _, 1, env, N₀, by omega, Eval.var env i, Steps.one _⟩
  | nil => exact ⟨.nil, 1, 1, env, N₀, by omega, Eval.nil env, Steps.one _⟩
  | const d => exact ⟨d, d.size, 1, env, N₀, by omega, Eval.const env d, Steps.one _⟩
  | cons h t =>
    simp only [step] at hN
    obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ := ih N₀ (by omega) h env (.cons1 t env :: k) r e hN
    -- the remaining run starts from the return to the `cons1` frame
    have hrest : step^[N₁] ⟨.ret r₁, e₁, .cons1 t env :: k⟩ = ⟨.ret r, e, []⟩ := by
      rw [hN₁, Nat.add_comm, Function.iterate_add_apply, s₁.1] at hN
      exact hN
    obtain ⟨N₂, rfl⟩ : ∃ N₂, N₁ = N₂ + 1 := by
      cases N₁ with
      | zero => simp at hrest
      | succ N₂ => exact ⟨N₂, rfl⟩
    rw [Function.iterate_succ_apply] at hrest
    simp only [step] at hrest
    obtain ⟨r₂, t₂, M₂, e₂, N₃, hN₃, h₂, s₂⟩ := ih N₂ (by omega) t env (.cons2 r₁ :: k) r e hrest
    have hrest₂ : step^[N₃] ⟨.ret r₂, e₂, .cons2 r₁ :: k⟩ = ⟨.ret r, e, []⟩ := by
      rw [hN₃, Nat.add_comm, Function.iterate_add_apply, s₂.1] at hrest
      exact hrest
    obtain ⟨N₄, rfl⟩ : ∃ N₄, N₃ = N₄ + 1 := by
      cases N₃ with
      | zero => simp at hrest₂
      | succ N₄ => exact ⟨N₄, rfl⟩
    refine ⟨.cons r₁ r₂, t₁ + t₂ + 1, 1 + M₁ + (1 + M₂) + 1, e₂, N₄, by omega,
      Eval.cons h₁ h₂, ?_⟩
    have := (((Steps.one ⟨.ev (.cons h t), env, k⟩).trans s₁).trans
      ((Steps.one ⟨.ret r₁, e₁, .cons1 t env :: k⟩).trans s₂)).trans
      (Steps.one ⟨.ret r₂, e₂, .cons2 r₁ :: k⟩)
    exact this.cast (by simp [stepCost]; omega)
  | elim i n c =>
    rcases hget : env.get i with _ | ⟨a, b⟩
    · simp only [step, hget] at hN
      obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ := ih N₀ (by omega) n env k r e hN
      refine ⟨r₁, t₁ + 1, 1 + M₁, e₁, N₁, by omega, Eval.elim_nil hget h₁, ?_⟩
      have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev n, env, k⟩ 1 := by
        have := Steps.one ⟨.ev (.elim i n c), env, k⟩
        simp only [step, stepCost, hget] at this
        exact this
      exact (h0.trans s₁).cast (by omega)
    · simp only [step, hget] at hN
      obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ :=
        ih N₀ (by omega) c (a :: b :: env) k r e hN
      refine ⟨r₁, t₁ + 1, 1 + M₁, e₁, N₁, by omega, Eval.elim_cons hget h₁, ?_⟩
      have h0 : Steps ⟨.ev (.elim i n c), env, k⟩ 1 ⟨.ev c, a :: b :: env, k⟩ 1 := by
        have := Steps.one ⟨.ev (.elim i n c), env, k⟩
        simp only [step, stepCost, hget] at this
        exact this
      exact (h0.trans s₁).cast (by omega)
  | let_ e' b =>
    simp only [step] at hN
    obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ := ih N₀ (by omega) e' env (.let1 b env :: k) r e hN
    have hrest : step^[N₁] ⟨.ret r₁, e₁, .let1 b env :: k⟩ = ⟨.ret r, e, []⟩ := by
      rw [hN₁, Nat.add_comm, Function.iterate_add_apply, s₁.1] at hN
      exact hN
    obtain ⟨N₂, rfl⟩ : ∃ N₂, N₁ = N₂ + 1 := by
      cases N₁ with
      | zero => simp at hrest
      | succ N₂ => exact ⟨N₂, rfl⟩
    rw [Function.iterate_succ_apply] at hrest
    simp only [step] at hrest
    obtain ⟨r₂, t₂, M₂, e₂, N₃, hN₃, h₂, s₂⟩ := ih N₂ (by omega) b (r₁ :: env) k r e hrest
    refine ⟨r₂, t₁ + t₂ + 1, 1 + M₁ + 1 + M₂, e₂, N₃, by omega, Eval.let_ h₁ h₂, ?_⟩
    have := (((Steps.one ⟨.ev (.let_ e' b), env, k⟩).trans s₁).trans
      (Steps.one ⟨.ret r₁, e₁, .let1 b env :: k⟩)).trans s₂
    exact this.cast (by simp [stepCost]; omega)
  | loop b =>
    simp only [step] at hN
    obtain ⟨r₁, t₁, M₁, e₁, N₁, hN₁, h₁, s₁⟩ := ih N₀ (by omega) b env (.loop1 b env :: k) r e hN
    have hrest : step^[N₁] ⟨.ret r₁, e₁, .loop1 b env :: k⟩ = ⟨.ret r, e, []⟩ := by
      rw [hN₁, Nat.add_comm, Function.iterate_add_apply, s₁.1] at hN
      exact hN
    obtain ⟨N₂, rfl⟩ : ∃ N₂, N₁ = N₂ + 1 := by
      cases N₁ with
      | zero => simp at hrest
      | succ N₂ => exact ⟨N₂, rfl⟩
    rw [Function.iterate_succ_apply] at hrest
    rcases r₁ with _ | ⟨_ | ⟨x, y⟩, v⟩
    · -- `loop_nil`
      simp only [step] at hrest
      refine ⟨.nil, t₁ + 1, 1 + M₁ + 1, env, N₂, by omega, Eval.loop_nil h₁, ?_⟩
      have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans s₁).trans
        (Steps.one ⟨.ret .nil, e₁, .loop1 b env :: k⟩)
      exact this.cast (by simp [stepCost])
    · -- `loop_stop`
      simp only [step] at hrest
      refine ⟨v, t₁ + 1, 1 + M₁ + 1, env, N₂, by omega, Eval.loop_stop h₁, ?_⟩
      have := ((Steps.one ⟨.ev (.loop b), env, k⟩).trans s₁).trans
        (Steps.one ⟨.ret (.cons .nil v), e₁, .loop1 b env :: k⟩)
      exact this.cast (by simp [stepCost])
    · -- `loop_step`: the continuation is the `loop` at the new environment
      simp only [step] at hrest
      have hrest' : step^[N₂ + 1] ⟨.ev (.loop b), v :: env.tail, k⟩ = ⟨.ret r, e, []⟩ := by
        rw [Function.iterate_succ_apply]
        exact hrest
      have hM₁ := s₁.ne_zero
      obtain ⟨r₂, t₂, M₂, e₂, N₃, hN₃, h₂, s₂⟩ :=
        ih (N₂ + 1) (by omega) (.loop b) (v :: env.tail) k r e hrest'
      obtain ⟨M₂', rfl⟩ := Nat.exists_eq_succ_of_ne_zero s₂.ne_zero
      obtain ⟨t₂', ht₂', s₂'⟩ := s₂.of_succ
      refine ⟨r₂, t₁ + t₂ + 1, 1 + M₁ + 1 + M₂', e₂, N₃, by omega, Eval.loop_step h₁ h₂, ?_⟩
      have := (((Steps.one ⟨.ev (.loop b), env, k⟩).trans s₁).trans
        (Steps.one ⟨.ret (.cons (.cons x y) v), e₁, .loop1 b env :: k⟩)).trans s₂'
      refine this.cast ?_
      simp only [stepCost] at ht₂' ⊢
      omega
