-- Prove2me | solution 1 for Malliavin.mderivD12_compPi
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:07:27.771596+00:00
-- url     : https://prove2.me/submissions/3cc0ae5e-3dc6-4f79-8aaf-c2a706845503

import Definitions.Def_Malliavin_DualDerivative
import Definitions.Def_Malliavin_ChainRule

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : ContDiff ℝ 1 f) {K : ℝ}
    (hK : ∀ y, ‖fderiv ℝ f y‖ ≤ K) (F : Fin n → D12 μ) :
    mderivD12 μ (D12.compPi μ hf hK F) =
      (memLp_grad_smul μ hf hK (fun i ↦ Lp.aestronglyMeasurable (F i : Lp ℝ 2 μ))
        (fun i ↦ mderivD12 μ (F i))).toLp _ :=
  (comp_pi_mem_domD12 μ hf hK fun i ↦ (F i).2).2
end Malliavin
