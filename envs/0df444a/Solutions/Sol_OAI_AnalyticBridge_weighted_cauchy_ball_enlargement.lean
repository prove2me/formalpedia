-- Prove2me | solution 1 for OAI.AnalyticBridge.weighted_cauchy_ball_enlargement
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:10:49.240205+00:00
-- url     : https://prove2.me/submissions/d39cdc53-2d0d-4d2f-9023-a3569daa6c4e

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinEmbedding
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_CubicNormalization
import Theorems.Thm_OAI_AnalyticBridge_reassembled_bilinear_bound
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.AnalyticBridge
namespace OAI.AnalyticBridge
theorem _root_.solution
    {Ω Λ : Type*} [DecidableEq Λ]
    (S : Finset Ω) (T : Finset Λ) (label : Ω → Λ)
    (w : Ω → ℂ) (A B : Λ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁)
    (hsupport : ∀ ω ∈ S, w ω ≠ 0 → label ω ∈ T)
    (hfiber : ∀ a ∈ T,
      (∑ ω ∈ S with label ω = a, ‖w ω‖) ≤ M₁)
    (hfiber₂ : ∀ a ∈ T,
      (∑ ω ∈ S with label ω = a, ‖w ω‖) ≤ M₂) :
    ‖∑ ω ∈ S, w ω * A (label ω) * star (B (label ω))‖ ^ 2 ≤
      (M₁ * ∑ a ∈ T, ‖A a‖ ^ 2) *
        (M₂ * ∑ a ∈ T, ‖B a‖ ^ 2) := by
  classical
  let S' : Finset Ω := S.filter (fun ω => w ω ≠ 0)
  have hmap : ∀ ω ∈ S', label ω ∈ T := by
    intro ω hω
    exact hsupport ω (Finset.mem_filter.mp hω).1 (Finset.mem_filter.mp hω).2
  have hsum :
      (∑ ω ∈ S', w ω * A (label ω) * star (B (label ω))) =
      (∑ ω ∈ S, w ω * A (label ω) * star (B (label ω))) := by
    dsimp [S']
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro ω hω
    by_cases hw : w ω = 0 <;> simp [hw]
  have hfiber' : ∀ a ∈ T,
      (∑ ω ∈ S' with label ω = a, ‖w ω‖) ≤ M₁ := by
    intro a ha
    have heq : (∑ ω ∈ S' with label ω = a, ‖w ω‖) =
        (∑ ω ∈ S with label ω = a, ‖w ω‖) := by
      dsimp [S']
      simp only [Finset.filter_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hl : label ω = a <;> by_cases hw : w ω = 0 <;> simp [hl, hw]
    rw [heq]
    exact hfiber a ha
  have hfiber₂' : ∀ a ∈ T,
      (∑ ω ∈ S' with label ω = a, ‖w ω‖) ≤ M₂ := by
    intro a ha
    have heq : (∑ ω ∈ S' with label ω = a, ‖w ω‖) =
        (∑ ω ∈ S with label ω = a, ‖w ω‖) := by
      dsimp [S']
      simp only [Finset.filter_filter, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases hl : label ω = a <;> by_cases hw : w ω = 0 <;> simp [hl, hw]
    rw [heq]
    exact hfiber₂ a ha
  rw [← hsum]
  exact reassembled_bilinear_bound S' T T label label w A B M₁ M₂
    hM₁ hmap hmap hfiber' hfiber₂'
end OAI.AnalyticBridge
