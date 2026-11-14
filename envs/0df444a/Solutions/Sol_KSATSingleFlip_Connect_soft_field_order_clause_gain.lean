-- Prove2me | solution 1 for KSATSingleFlip.Connect.soft_field_order_clause_gain
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T10:36:46.569195+00:00
-- url     : https://prove2.me/submissions/366c9aa6-9b9f-4d6d-ba7b-ab84c027aa19

import Theorems.Thm_KSATSingleFlip_Connect_soft_clause_gain_concave
import Theorems.Thm_KSATSingleFlip_Connect_soft_clause_gain_continuous
import Mathlib
set_option autoImplicit false
open MeasureTheory KSATSingleFlip.Connect Set

theorem solution (ν' ν : Measure ℝ) (hord : softFieldLE ν' ν)
    (ψ : ℝ → ℝ) (hc : ContinuousOn ψ (Icc 0 1)) (hψ : ConcaveOn ℝ (Icc 0 1) ψ)
    (hψ0 : ψ 0 = 0) (hψ1 : ψ 1 = 0) (v0 v1 : ℝ) (hv0 : 0 ≤ v0) (hv1 : 0 ≤ v1) :
    pairing (fun q => softClauseGain ψ v0 v1 (1-q)) ν' ≤
      pairing (fun q => softClauseGain ψ v0 v1 (1-q)) ν := by
  have hgain := soft_clause_gain_concave ψ hψ hψ0 hψ1 v0 v1 hv0 hv1
  have hcont := soft_clause_gain_continuous ψ hc hψ0 hψ1 v0 v1 hv0 hv1
  have hmap : MapsTo (fun q : ℝ => 1-q) (Icc 0 1) (Icc 0 1) := by
    intro q hq
    constructor <;> linarith [hq.1,hq.2]
  have hc' : ContinuousOn (fun q : ℝ => softClauseGain ψ v0 v1 (1-q)) (Icc 0 1) := by
    apply hcont.comp _ hmap
    fun_prop
  have hconc : ConcaveOn ℝ (Icc 0 1) (fun q => softClauseGain ψ v0 v1 (1-q)) := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro x hx y hy a b ha hb hab
    have hh := hgain.1.2 (hmap hx) (hmap hy) ha hb hab
    simp only [smul_eq_mul] at hh ⊢
    have heq : a*(1-x)+b*(1-y) = 1-(a*x+b*y) := by nlinarith
    rwa [heq] at hh
  apply hord (fun q => softClauseGain ψ v0 v1 (1-q)) hc' hconc
  · simpa using hgain.2.2
  · simpa using hgain.2.1
