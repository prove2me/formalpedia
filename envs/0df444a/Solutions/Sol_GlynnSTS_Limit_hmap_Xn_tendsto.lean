-- Prove2me | solution 1 for GlynnSTS.Limit.hmap_Xn_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T19:42:06.461684+00:00
-- url     : https://prove2.me/submissions/cc85958d-7b6b-46fb-a507-589c1eaab9ae

import Mathlib
import Definitions.Def_GlynnSTS_Limit_Setting
import Theorems.Thm_GlynnSTS_Limit_sigmaB_mem_D_hmap_null

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace GlynnSTSAux

/-- Continuous mapping theorem for maps continuous at almost every point of the limit. -/
theorem cmt_ae {Ω E : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {X : ℕ → Ω → E} {Z : Ω → E} {h : E → ℝ} (hh : Measurable h)
    (hX : TendstoInDistribution X atTop Z (fun _ => P) P)
    (hD : P {ω | ¬ ContinuousAt h (Z ω)} = 0) :
    TendstoInDistribution (fun n ω => h (X n ω)) atTop (fun ω => h (Z ω)) (fun _ => P) P := by
  refine ⟨fun n => hh.comp_aemeasurable (hX.forall_aemeasurable n),
    hh.comp_aemeasurable hX.aemeasurable_limit, ?_⟩
  apply MeasureTheory.tendsto_of_forall_isOpen_le_liminf'
  intro G hG
  simp only [ProbabilityMeasure.coe_mk]
  set U := interior (h ⁻¹' G) with hU
  have hUo : IsOpen U := isOpen_interior
  have hsub : h ⁻¹' G ⊆ U ∪ {x | ¬ ContinuousAt h x} := by
    intro x hx
    by_cases hc : ContinuousAt h x
    · left; exact mem_interior_iff_mem_nhds.2 (hc.preimage_mem_nhds (hG.mem_nhds hx))
    · right; exact hc
  have hlim := ProbabilityMeasure.le_liminf_measure_open_of_tendsto hX.tendsto hUo
  simp only [ProbabilityMeasure.coe_mk] at hlim
  have hZa := hX.aemeasurable_limit
  calc P.map (fun ω => h (Z ω)) G = P ((fun ω => h (Z ω)) ⁻¹' G) :=
        Measure.map_apply_of_aemeasurable (hh.comp_aemeasurable hZa) hG.measurableSet
    _ ≤ P (Z ⁻¹' U ∪ {ω | ¬ ContinuousAt h (Z ω)}) := measure_mono (fun ω hω => hsub hω)
    _ ≤ P (Z ⁻¹' U) + P {ω | ¬ ContinuousAt h (Z ω)} := measure_union_le _ _
    _ = P.map Z U := by
        rw [hD, add_zero, Measure.map_apply_of_aemeasurable hZa hUo.measurableSet]
    _ ≤ liminf (fun n => P.map (X n) U) atTop := hlim
    _ ≤ liminf (fun n => P.map (fun ω => h (X n ω)) G) atTop := by
        refine liminf_le_liminf ?_ (by isBoundedDefault) (by isBoundedDefault)
        filter_upwards with n
        rw [Measure.map_apply_of_aemeasurable (hX.forall_aemeasurable n) hUo.measurableSet]
        exact (measure_mono (μ := P) (s := X n ⁻¹' U) (t := (h ∘ X n) ⁻¹' G)
          (fun ω hω => interior_subset (s := h ⁻¹' G) hω)).trans_eq
          (Measure.map_apply_of_aemeasurable (hh.comp_aemeasurable (hX.forall_aemeasurable n))
            hG.measurableSet).symm

end GlynnSTSAux

open GlynnSTS.Limit in
theorem solution {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Ω → C(unitInterval, ℝ)) (hB : IsStdBMC P B)
    (Y : ℝ → Ω → ℝ) (Ybar : ℕ → Ω → C(unitInterval, ℝ)) (μ σ : ℝ)
    (h21 : Assumption21 P Y Ybar μ σ B)
    (g : C(unitInterval, ℝ) → ℝ) (hg : ClassM P B g) :
    TendstoInDistribution (fun (n : ℕ) ω => hmap g (Xn Ybar μ n ω)) atTop
      (fun ω => hmap g (σ • B ω)) (fun _ => P) P := by
  have hgm : Measurable g := hg.1
  have hev : Measurable (fun x : C(unitInterval, ℝ) => x 1) :=
    (continuous_eval_const (1 : unitInterval)).measurable
  have hhm : Measurable (hmap g) := by
    unfold hmap
    refine Measurable.ite ?_ (hev.div hgm) measurable_const
    exact (hgm (measurableSet_singleton 0)).compl
  exact GlynnSTSAux.cmt_ae hhm h21.fclt
    (sigmaB_mem_D_hmap_null P B hB g hg σ h21.sigma_pos)
