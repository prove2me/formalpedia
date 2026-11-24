-- Prove2me | solution 1 for Kyprianou.Ch02.identDistribPairOfAELimitsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T23:36:57.943517+00:00
-- url     : https://prove2.me/submissions/7f50510e-a9f0-4839-b95b-75211c88e631

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (F G : ℕ → Ω → ℝ × ℝ) (f g : Ω → ℝ × ℝ)
    (hLaw : ∀ n, IdentDistrib (F n) (G n) P P)
    (hf : ∀ᵐ ω ∂P, Tendsto (fun n => F n ω) atTop (nhds (f ω)))
    (hg : ∀ᵐ ω ∂P, Tendsto (fun n => G n ω) atTop (nhds (g ω))) :
    IdentDistrib f g P P := by
  have hmF : ∀ n, AEMeasurable (F n) P := fun n => (hLaw n).aemeasurable_fst
  have hmG : ∀ n, AEMeasurable (G n) P := fun n => (hLaw n).aemeasurable_snd
  have hmf := aemeasurable_of_tendsto_metrizable_ae' hmF hf
  have hmg := aemeasurable_of_tendsto_metrizable_ae' hmG hg
  have hF := (tendstoInDistribution_of_ae_tendsto hmF hmf hf).tendsto
  have hG := (tendstoInDistribution_of_ae_tendsto hmG hmg hg).tendsto
  have hEq : (fun n => (⟨P.map (F n), Measure.isProbabilityMeasure_map (hmF n)⟩ :
      ProbabilityMeasure (ℝ × ℝ))) =
      (fun n => (⟨P.map (G n), Measure.isProbabilityMeasure_map (hmG n)⟩ :
        ProbabilityMeasure (ℝ × ℝ))) := by
    funext n
    exact Subtype.ext (hLaw n).map_eq
  rw [hEq] at hF
  exact ⟨hmf, hmg, congrArg (fun μ : ProbabilityMeasure (ℝ × ℝ) => (μ : Measure (ℝ × ℝ)))
    (tendsto_nhds_unique hF hG)⟩
