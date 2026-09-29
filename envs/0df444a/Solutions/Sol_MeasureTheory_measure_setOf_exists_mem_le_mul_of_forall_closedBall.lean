-- Prove2me | solution 1 for MeasureTheory.measure_setOf_exists_mem_le_mul_of_forall_closedBall
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/2b99827c-d666-5623-8517-0b4694bef5ff

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall

open MeasureTheory Metric Set
open scoped ENNReal NNReal

theorem solution
    {α β : Type*} [MetricSpace α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    [HasBesicovitchCovering α] {_ : MeasurableSpace β} (μ : Measure β) (ν : Measure α) [SFinite ν]
    [ν.OuterRegular] (P : β → α → Prop) (S : Set α) (K : ℝ≥0∞) (hK : K ≠ ⊤)
    (h : ∀ x ∈ S, ∃ δ > 0, ∀ ρ ∈ Set.Ioo 0 δ,
      μ {b | ∃ y ∈ Metric.closedBall x ρ, P b y} ≤ K * ν (Metric.closedBall x ρ)) :
    μ {b | ∃ x ∈ S, P b x} ≤ K * ν S := by
  classical
  choose! δ hδpos hδ using h
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  obtain ⟨η, hηpos, hη⟩ := ENNReal.exists_nnreal_pos_mul_lt hK (ENNReal.coe_pos.2 hε).ne'
  obtain ⟨t, r, tcount, tS, hr, hcover, hsum⟩ :=
    Besicovitch.exists_closedBall_covering_tsum_measure_le ν (ENNReal.coe_pos.2 hηpos).ne'
      (fun x => Set.Ioo 0 (δ x)) S (fun x hx ρ' hρ' =>
        ⟨min (δ x) ρ' / 2,
          ⟨by have := hδpos x hx; positivity, by linarith [min_le_left (δ x) ρ', hδpos x hx]⟩,
          ⟨by have := hδpos x hx; positivity, by linarith [min_le_right (δ x) ρ', hδpos x hx]⟩⟩)
  calc μ {b | ∃ x ∈ S, P b x}
      ≤ μ (⋃ x ∈ t, {b | ∃ y ∈ closedBall x (r x), P b y}) := by
        refine measure_mono fun b hb => ?_
        obtain ⟨x, hxS, hPbx⟩ := hb
        obtain ⟨x', hx't, hxx'⟩ := Set.mem_iUnion₂.1 (hcover hxS)
        exact Set.mem_iUnion₂.2 ⟨x', hx't, x, hxx', hPbx⟩
    _ ≤ ∑' x : t, μ {b | ∃ y ∈ closedBall (x : α) (r x), P b y} := measure_biUnion_le μ tcount _
    _ ≤ ∑' x : t, K * ν (closedBall (x : α) (r x)) :=
        ENNReal.tsum_le_tsum fun x => hδ x (tS x.2) (r x) (hr x x.2)
    _ = K * ∑' x : t, ν (closedBall (x : α) (r x)) := ENNReal.tsum_mul_left
    _ ≤ K * (ν S + η) := by gcongr
    _ = K * ν S + η * K := by rw [mul_add, mul_comm K (η : ℝ≥0∞)]
    _ ≤ K * ν S + ε := by gcongr

end S_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall
end P2MW
export P2MW.S_MeasureTheory_measure_setOf_exists_mem_le_mul_of_forall_closedBall (solution)
