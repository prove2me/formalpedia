-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.monotone_integral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:29.257038+00:00
-- url     : https://prove2.me/submissions/675f9965-323a-4ef9-85f9-3f1526e30683

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth_of_holderConjugate
public import Theorems.Thm_NemytskiiLebesgue_Real_HolderConjugate_integrable_memLp_inner_memLp


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Ω → E → E} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C : ℝ} (hC : 0 ≤ C)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : E, ‖f ω ξ‖ ≤ |a ω| + C * ‖ξ‖ ^ (p / q))
    (hf0 : ∀ᵐ ω ∂μ, ∀ s t : E, ⟪f ω s - f ω t, s - t⟫ ≥ 0)
    {u : Ω → E} (hup : MemLp u ↱p μ)
    {v : Ω → E} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ ∧
    0 ≤ ∫ ω : Ω, ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫ ∂μ := by
  constructor
  · apply Real.HolderConjugate.integrable_memLp_inner_memLp hpq
    · apply MemLp.sub <;> apply hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC hfaCpq
      <;> assumption
    · exact MemLp.sub hup hvp
  · apply integral_nonneg_of_ae
    filter_upwards [hf0] with ω hω
    exact hω (u ω) (v ω)
end IsCaratheodory
end NemytskiiLebesgue
