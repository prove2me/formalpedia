-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.memLp_nemytskii_ofReal_of_growth_of_holderConjugate_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:30.088074+00:00
-- url     : https://prove2.me/submissions/85827907-6a8e-4b54-acbb-e34ffbe1f836

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth_of_holderConjugate


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
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) ↱q μ :=
  hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC₁ hfaCpq hup
end IsCaratheodory
end NemytskiiLebesgue
