-- Prove2me | solution 1 for MarkovChainCLT.chainMeasure_map_shift
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T20:19:20.098034+00:00
-- url     : https://prove2.me/submissions/668b6835-1634-4630-848a-1d3f3887353c

import Definitions.Def_MarkovChainPathMeasure
import Mathlib.Probability.Kernel.Invariance
import Theorems.Thm_MarkovChainCLT_markovChainKernel_map_shift

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory
open MarkovChainCLT

theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (hinv : Kernel.Invariant P π) :
    (chainMeasure P π).map (fun ω : ℕ → X => fun n => ω (n + 1)) = chainMeasure P π := by
  have hσ : Measurable (fun (ω : ℕ → X) => fun n => ω (n + 1)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  rw [chainMeasure, Measure.map_comp _ _ hσ, markovChainKernel_map_shift,
    ← Measure.comp_assoc]
  have h : P ∘ₘ π = π := hinv
  rw [h]
