-- Prove2me | solution 1 for Malliavin.mem_domD12_of_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:05:15.228829+00:00
-- url     : https://prove2.me/submissions/4263a641-8b4c-454a-b69e-657ab09d3936

import Definitions.Def_Malliavin_CameronMartinTheorem
import Definitions.Def_Malliavin_MalliavinDerivative

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
universe u_1 u_2 u_3 u_4 u_5
open Malliavin
open CameronMartin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  (μ : Measure W) [IsGaussian μ]
namespace Malliavin
theorem _root_.solution {F : ℕ → Lp ℝ 2 μ} (hF : ∀ n, F n ∈ domD12 μ)
    {F₀ : Lp ℝ 2 μ} {η₀ : Lp (Space μ) 2 μ} (hF₀ : Tendsto F atTop (𝓝 F₀))
    (hη : Tendsto (fun n ↦ mderivClosure μ (F n)) atTop (𝓝 η₀)) :
    F₀ ∈ domD12 μ ∧ mderivClosure μ F₀ = η₀ := by
  have hcl := InGraphClosure.of_tendsto μ (fun n ↦ inGraphClosure_mderivClosure μ (hF n)) hF₀ hη
  exact ⟨⟨η₀, hcl⟩, mderivClosure_eq μ hcl⟩
end Malliavin
