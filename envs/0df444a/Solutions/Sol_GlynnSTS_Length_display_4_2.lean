-- Prove2me | solution 1 for GlynnSTS.Length.display_4_2
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T10:39:09.475127+00:00
-- url     : https://prove2.me/submissions/36e1e80f-e132-41c5-848f-a7018a9e3abf

import Mathlib
import Definitions.Def_GlynnSTS_Length_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : GlynnSTS.Limit.IsStdBMC P B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : GlynnSTS.Limit.ClassM P B g)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ))
    (μ σ : ℝ) (h21 : GlynnSTS.Length.Assumption21 P Y Ybar μ σ B) :
    TendstoInDistribution (fun (n : ℕ) ω => g (GlynnSTS.Limit.Xn Ybar μ n ω)) atTop
      (fun ω => σ * g (B ω)) (fun _ => P) P := by
  have hσ : 0 < σ := h21.sigma_pos
  have hfc := h21.fclt
  have hlim : (fun ω => σ * g (B ω)) = fun ω => g (σ • B ω) := by
    funext ω; rw [hg.2.1 σ hσ]
  rw [hlim]
  have hgm : Measurable g := hg.1
  have hDm : MeasurableSet (GlynnSTS.Limit.D g) :=
    (IsGδ.setOfPred_continuousAt g).measurableSet.compl
  -- continuity of `g` at `σ • x` is equivalent to continuity at `x`
  have hcont : ∀ x, ContinuousAt g (σ • x) ↔ ContinuousAt g x := by
    intro x
    constructor
    · intro h
      have hfun : g = fun y => σ⁻¹ * g (σ • y) := by
        funext y; rw [hg.2.1 σ hσ, ← mul_assoc, inv_mul_cancel₀ hσ.ne', one_mul]
      rw [hfun]
      exact continuousAt_const.mul (h.comp (continuous_const_smul σ).continuousAt)
    · intro h
      have hfun : g = fun y => σ * g (σ⁻¹ • y) := by
        funext y; rw [hg.2.1 σ⁻¹ (inv_pos.2 hσ), ← mul_assoc, mul_inv_cancel₀ hσ.ne', one_mul]
      rw [hfun]
      refine continuousAt_const.mul (ContinuousAt.comp_of_eq h
        (continuous_const_smul σ⁻¹).continuousAt ?_)
      rw [smul_smul, inv_mul_cancel₀ hσ.ne', one_smul]
  have hD0 : P ((fun ω => σ • B ω) ⁻¹' GlynnSTS.Limit.D g) = 0 := by
    have : (fun ω => σ • B ω) ⁻¹' GlynnSTS.Limit.D g = {ω | B ω ∈ GlynnSTS.Limit.D g} := by
      ext ω
      simp only [Set.mem_preimage, Set.mem_setOf_eq, GlynnSTS.Limit.D, hcont]
    rw [this]; exact hg.2.2.2.2
  refine ⟨fun n => hgm.comp_aemeasurable (hfc.forall_aemeasurable n),
    hgm.comp_aemeasurable hfc.aemeasurable_limit, ?_⟩
  apply MeasureTheory.tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  simp only [ProbabilityMeasure.coe_mk]
  have hGm : MeasurableSet G := hG.measurableSet
  have hint : IsOpen (interior (g ⁻¹' G)) := isOpen_interior
  have hsub : g ⁻¹' G ⊆ interior (g ⁻¹' G) ∪ GlynnSTS.Limit.D g := by
    intro x hx
    by_cases hx' : ContinuousAt g x
    · left
      rw [mem_interior_iff_mem_nhds]
      exact hx'.preimage_mem_nhds (hG.mem_nhds hx)
    · right; exact hx'
  have hopen := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hfc.tendsto hint
  simp only [ProbabilityMeasure.coe_mk] at hopen
  rw [Measure.map_apply_of_aemeasurable hfc.aemeasurable_limit hint.measurableSet] at hopen
  have hZm : AEMeasurable (fun ω => g (σ • B ω)) P := hgm.comp_aemeasurable hfc.aemeasurable_limit
  have hXm : ∀ n, AEMeasurable (fun ω => g (GlynnSTS.Limit.Xn Ybar μ n ω)) P :=
    fun n => hgm.comp_aemeasurable (hfc.forall_aemeasurable n)
  rw [Measure.map_apply_of_aemeasurable hZm hGm]
  calc P ((fun ω => g (σ • B ω)) ⁻¹' G)
      ≤ P ((fun ω => σ • B ω) ⁻¹' interior (g ⁻¹' G)) +
          P ((fun ω => σ • B ω) ⁻¹' GlynnSTS.Limit.D g) := by
        refine (measure_mono ?_).trans (measure_union_le _ _)
        intro ω hω; exact hsub hω
    _ = P ((fun ω => σ • B ω) ⁻¹' interior (g ⁻¹' G)) := by rw [hD0, add_zero]
    _ ≤ _ := hopen
    _ ≤ _ := by
        refine liminf_le_liminf (Eventually.of_forall (fun n => ?_))
        rw [Measure.map_apply_of_aemeasurable (hfc.forall_aemeasurable n) hint.measurableSet,
          Measure.map_apply_of_aemeasurable (hXm n) hGm]
        exact measure_mono (fun ω (hω : GlynnSTS.Limit.Xn Ybar μ n ω ∈ interior (g ⁻¹' G)) =>
          (interior_subset (s := g ⁻¹' G) hω : g (GlynnSTS.Limit.Xn Ybar μ n ω) ∈ G))
