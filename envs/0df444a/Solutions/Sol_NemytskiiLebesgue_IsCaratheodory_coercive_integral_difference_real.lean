-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.coercive_integral_difference_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:40:53.503493+00:00
-- url     : https://prove2.me/submissions/462a6842-4439-413e-b99c-6e0aad20dc41

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_coercive_integral_difference

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
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hfCp : ∀ᵐ ω ∂μ, ∀ ξ η : ℝ^k, ⟪f ω ξ - f ω η, ξ - η⟫ ≥ C₂ * ‖ξ - η‖ ^ p)
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ^k} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ ∧
    ∫ ω : Ω, ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫ ∂μ ≥ C₂ * ∫ ω : Ω, ‖u ω - v ω‖ ^ p ∂μ :=
  hf.coercive_integral_difference hpq haq hC₁ hfaCpq hC₂ hfCp hup hvp
end IsCaratheodory
end NemytskiiLebesgue
