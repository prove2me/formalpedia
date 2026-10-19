-- Prove2me | solution 1 for OAI.C0Absorption.localOp_support_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T22:24:57.150825+00:00
-- url     : https://prove2.me/submissions/6942a908-5ce0-47c4-9d3e-f2eaf5b76284

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology


theorem solution {X : Type*} [PseudoMetricSpace X] (isG : Bool) (q : X)
    {ε : ℝ} (hε : 0 < ε) (u v : X → ℝ) {K : ℝ≥0} (hv : LipschitzWith K v)
    (a : ℝ) (ha : ∀ x ∈ tsupport u, v x ≤ a) :
    ∀ x ∈ tsupport (localOp isG q ε u), v x ≤ a+ε*K := by
  have hK0 : (0:ℝ) ≤ ε * K := by positivity
  have hfar : ∀ x, ε < dist x q → localOp isG q ε u x = if isG then u x else 0 := by
    intro x hx
    have ht : 1 ≤ dist x q / ε := by rw [le_div_iff₀ hε]; linarith
    have hchi : chi (dist x q / ε) = 1 := by
      unfold chi; rw [min_eq_left]; exact le_max_of_le_right (by linarith)
    cases isG <;> simp [localOp, localGLinear, localRLinear, localR, localG, hchi]
  by_cases huq : u q = 0
  · have hsub : Function.support (localOp isG q ε u) ⊆ Function.support u := by
      intro x hx
      by_contra hux
      simp only [Function.mem_support, not_not] at hux hx
      apply hx
      cases isG <;> simp [localOp, localGLinear, localRLinear, localR, localG, hux, huq]
    intro x hx
    have := ha x (closure_mono hsub hx)
    linarith
  · have hq : q ∈ tsupport u := subset_tsupport _ huq
    have hS : IsClosed (tsupport u ∪ Metric.closedBall q ε) := (isClosed_tsupport _).union Metric.isClosed_closedBall
    have hsub : Function.support (localOp isG q ε u) ⊆ tsupport u ∪ Metric.closedBall q ε := by
      intro x hx
      by_contra hn
      simp only [Set.mem_union, not_or, Metric.mem_closedBall, not_le] at hn
      have hux : u x = 0 := image_eq_zero_of_notMem_tsupport hn.1
      apply hx
      rw [hfar x hn.2]; simp [hux]
    intro x hx
    rcases closure_minimal hsub hS hx with h | h
    · have := ha x h; linarith
    · have h1 := hv.dist_le_mul x q
      have h2 := ha q hq
      rw [Metric.mem_closedBall] at h
      have h3 : v x - v q ≤ K * dist x q := le_trans (le_abs_self _) (by rw [← Real.dist_eq]; exact h1)
      have h4 : (K:ℝ) * dist x q ≤ K * ε := mul_le_mul_of_nonneg_left h K.2
      linarith

