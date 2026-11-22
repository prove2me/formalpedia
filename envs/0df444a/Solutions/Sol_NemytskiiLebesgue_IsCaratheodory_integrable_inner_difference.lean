-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.integrable_inner_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:28.704689+00:00
-- url     : https://prove2.me/submissions/688c0646-2d10-4b2e-8981-349f5df462de

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth_of_holderConjugate
public import Theorems.Thm_NemytskiiLebesgue_Real_HolderConjugate_integrable_memLp_inner_memLp


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Ω → E → E} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : E, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {u : Ω → E} (hup : MemLp u ↱p μ)
    {v : Ω → E} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ :=
  Real.HolderConjugate.integrable_memLp_inner_memLp hpq
    (MemLp.sub
      (hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC₁ hfaCpq hup)
      (hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC₁ hfaCpq hvp)
    ) (MemLp.sub hup hvp)
end IsCaratheodory
end NemytskiiLebesgue
