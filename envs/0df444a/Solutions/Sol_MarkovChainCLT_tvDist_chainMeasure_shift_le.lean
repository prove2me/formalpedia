-- Prove2me | solution 1 for MarkovChainCLT.tvDist_chainMeasure_shift_le
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-08-15T22:05:50.820335+00:00
-- url     : https://prove2.me/submissions/6ef9e80e-6aca-4392-a4a1-0a90590d8a49

import Theorems.Thm_MarkovChainCLT_tvDist_comp_le
import Theorems.Thm_MarkovChainCLT_tvDist_comp_le_of_forall
import Theorems.Thm_MarkovChainCLT_markovChainKernel_map_shift_iter

open MeasureTheory ProbabilityTheory
open MarkovChainCLT
open scoped ENNReal NNReal

set_option maxHeartbeats 1000000

/-- The chain from `lam`, observed from time `m` on, is within `C` of the stationary
chain in total variation on path space. -/
theorem solution {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (π : Measure X) [IsProbabilityMeasure π]
    (lam : Measure X) [IsProbabilityMeasure lam] (m : ℕ) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ x, tvDist (iterKernel P m x) π ≤ C) :
    tvDist ((chainMeasure P lam).map (fun ω : ℕ → X => fun n => ω (n + m)))
      (chainMeasure P π) ≤ C := by
  set K := BanditAlgorithm.markovChainKernel P with hK
  have hσ : Measurable (fun (ω : ℕ → X) => fun n => ω (n + m)) :=
    measurable_pi_lambda _ (fun _ => measurable_pi_apply _)
  haveI : IsProbabilityMeasure ((iterKernel P m) ∘ₘ lam) := inferInstance
  -- the shifted chain is the chain started from `Pᵐ ∘ₘ lam`
  have hshift : (chainMeasure P lam).map (fun ω : ℕ → X => fun n => ω (n + m))
      = K ∘ₘ ((iterKernel P m) ∘ₘ lam) := by
    rw [chainMeasure, ← hK, Measure.map_comp _ _ hσ,
      MarkovChainCLT.markovChainKernel_map_shift_iter P m, ← Measure.comp_assoc]
  rw [hshift, show chainMeasure P π = K ∘ₘ π from rfl]
  -- data processing, then the initial-distribution transfer
  refine le_trans (MarkovChainCLT.tvDist_comp_le K ((iterKernel P m) ∘ₘ lam) π) ?_
  exact MarkovChainCLT.tvDist_comp_le_of_forall (iterKernel P m) lam π C hC0 hC
