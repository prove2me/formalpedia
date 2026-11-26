-- Prove2me | solution 1 for Kyprianou.Ch04.boundedRewardLimitSupport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:49:59.472987+00:00
-- url     : https://prove2.me/submissions/9cdfa0d6-c83c-4df3-8e88-cc9d23d55bba

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_positiveRewardInfimumSupportBounds
import Theorems.Thm_Kyprianou_Ch04_boundedAntitoneRewardIntegralLimit
import Theorems.Thm_Kyprianou_Ch04_antitoneRewardMeanProperties
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Limiting means of bounded decreasing rewards are supported on their positive event. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : NNReal × Ω → ℝ) (hg : Measurable g)
    (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    (hga : ∀ w, Antitone (fun t : NNReal => g (t,w)))
    (B : Set Ω) (hB : ∀ w, w ∈ B ↔ 0 < ⨅ n : ℕ, g ((n : NNReal),w)) :
    let f : NNReal → ℝ := fun t => ∫ w, g (t,w) ∂P
    MeasurableSet B ∧
      (∀ ell : ℝ, Tendsto f atTop (nhds ell) → ell ≤ (P B).toReal) ∧
      (P B = 0 → Tendsto f atTop (nhds 0)) := by
  intro f
  let a : ℕ → Ω → ℝ := fun n w => g ((n : NNReal),w)
  have hm (n : ℕ) : Measurable (a n) := hg.comp (measurable_const.prodMk measurable_id)
  have ha (w : Ω) : Antitone (fun n => a n w) := fun n k hnk => hga w (by exact_mod_cast hnk)
  obtain ⟨hBm,hbound,hzero⟩ := Kyprianou.Ch04.positiveRewardInfimumSupportBounds P a hm
    (fun n w => hg0 _) (fun n w => hg1 _) B hB
  have hseq := Kyprianou.Ch04.boundedAntitoneRewardIntegralLimit P a hm
    (fun n w => hg0 _) (fun n w => hg1 _) ha
  have hcast : Tendsto (fun n : ℕ => (n : NNReal)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨hBm,?_ ,?_⟩
  · intro ell hlim
    have heq := tendsto_nhds_unique (hlim.comp hcast) hseq
    rw [heq]
    exact hbound
  · intro hnull
    obtain ⟨_,_,_,_,ell,_,hlim⟩ := Kyprianou.Ch04.antitoneRewardMeanProperties P g hg hg0 hg1 hga
    have heq := tendsto_nhds_unique (hlim.comp hcast) hseq
    rw [heq,hzero hnull] at hlim
    exact hlim
