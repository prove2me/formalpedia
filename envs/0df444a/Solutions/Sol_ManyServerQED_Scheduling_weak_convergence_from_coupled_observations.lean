-- Prove2me | solution 1 for ManyServerQED.Scheduling.weak_convergence_from_coupled_observations
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T01:09:26.337648+00:00
-- url     : https://prove2.me/submissions/0ce2e364-1174-42ae-bf08-c8f979fa82b8

import Mathlib

open MeasureTheory ProbabilityTheory Filter Topology

theorem solution
    {Ω Ω' E D : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace D] [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    (X : ℕ → Ω → D) (X' : ℕ → Ω' → D)
    (hLaw : ∀ n, IdentDistrib (X n) (X' n) P P')
    (G : D → E) (hG : Measurable G)
    (L : Ω' → E) (hL : AEMeasurable L P')
    (hlim : ∀ᵐ ω ∂P', Tendsto (fun n => G (X' n ω)) atTop (𝓝 (L ω))) :
    TendstoInDistribution (fun n ω => G (X n ω)) atTop L (fun _ => P) P' := by
  have h' := tendstoInDistribution_of_ae_tendsto
    (fun n => hG.comp_aemeasurable (hLaw n).aemeasurable_snd) hL hlim
  refine ⟨fun n => hG.comp_aemeasurable (hLaw n).aemeasurable_fst, hL, ?_⟩
  refine h'.tendsto.congr (fun n => ?_)
  exact Subtype.ext ((hLaw n).comp hG).map_eq.symm
