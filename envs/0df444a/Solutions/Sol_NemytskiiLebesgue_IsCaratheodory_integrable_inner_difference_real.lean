-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.integrable_inner_difference_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:40:16.827172+00:00
-- url     : https://prove2.me/submissions/1c6f04bc-2ef7-4857-ad6b-662eaa120427

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
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} (hf : IsCaratheodory f μ)
    {p q : ℝ} (hpq : Real.HolderConjugate p q)
    {a : Ω → ℝ} (haq : MemLp a ↱q μ)
    {C₁ : ℝ} (hC₁ : 0 ≤ C₁)
    (hfaCpq : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ‖f ω ξ‖ ≤ |a ω| + C₁ * ‖ξ‖ ^ (p / q))
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ)
    {v : Ω → ℝ^k} (hvp : MemLp v ↱p μ) :
    Integrable (fun ω : Ω => ⟪f ω (u ω) - f ω (v ω), u ω - v ω⟫) μ :=
  hf.integrable_inner_difference hpq haq hC₁ hfaCpq hup hvp
end IsCaratheodory
end NemytskiiLebesgue
