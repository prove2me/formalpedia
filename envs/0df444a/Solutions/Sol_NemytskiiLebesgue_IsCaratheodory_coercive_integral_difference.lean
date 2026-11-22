-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.coercive_integral_difference
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:40:15.949896+00:00
-- url     : https://prove2.me/submissions/9dc22b57-023f-4e45-9e16-7f669a719d20

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_integrable_inner_difference

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
    {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hfCp : ∀ᵐ ω ∂μ, ∀ ξ η : E, ⟪f ω ξ - f ω η, ξ - η⟫ ≥ C₂ * ‖ξ - η‖ ^ p)
    {u : Ω → E} (hup : MemLp u ↱p μ)
    {v : Ω → E} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ ∧
    ∫ ω : Ω, ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫ ∂μ ≥ C₂ * ∫ ω : Ω, ‖u ω - v ω‖ ^ p ∂μ := by
  constructor
  · exact hf.integrable_inner_difference hpq haq hC₁ hfaCpq hup hvp
  · rw [←integral_const_mul]
    apply integral_mono_of_nonneg
    · exact Filter.Eventually.of_forall ↓(mul_nonneg hC₂.le (Real.rpow_nonneg (norm_nonneg _) _))
    · apply_rules [IsCaratheodory.integrable_inner_difference]
    · filter_upwards [hfCp] with ω hω
      apply hω
end IsCaratheodory
end NemytskiiLebesgue
