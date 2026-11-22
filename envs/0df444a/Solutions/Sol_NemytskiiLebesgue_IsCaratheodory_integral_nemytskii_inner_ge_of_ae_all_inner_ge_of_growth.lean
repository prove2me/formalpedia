-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.integral_nemytskii_inner_ge_of_ae_all_inner_ge_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:29.663304+00:00
-- url     : https://prove2.me/submissions/e51a9cd6-7fa5-43f4-ad0b-7ca49adff2d1

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_integral_inner_ge_of_ae_inner_ge_of_integrable
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_memLp_nemytskii_of_growth_of_holderConjugate
public import Theorems.Thm_NemytskiiLebesgue_Real_HolderConjugate_integrable_memLp_inner_memLp
public import Theorems.Thm_NemytskiiLebesgue_integrable_norm_rpow_of_memLp


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
    {b : Ω → ℝ} (hb1 : Integrable b μ)
    {C₂ : ℝ} (hfCpb : ∀ᵐ ω ∂μ, ∀ ξ : ℝ^k, ⟪f ω ξ, ξ⟫ ≥ C₂ * ‖ξ‖ ^ p - b ω)
    {u : Ω → ℝ^k} (hup : MemLp u ↱p μ) :
    MemLp (fun ω : Ω => f ω (u ω)) ↱q μ ∧
    Integrable (fun ω : Ω => ⟪f ω (u ω), u ω⟫) μ ∧
    ∫ ω : Ω, ⟪f ω (u ω), u ω⟫ ∂μ ≥ C₂ * ∫ ω : Ω, ‖u ω‖ ^ p ∂μ - ∫ ω : Ω, |b ω| ∂μ :=
  have hp : 1 < p :=
    Real.HolderTriple.lt hpq
  have hwd : MemLp (fun ω : Ω => f ω (u ω)) ↱q μ :=
    hf.memLp_nemytskii_of_growth_of_holderConjugate hpq haq hC₁ hfaCpq hup
  have hinteg : Integrable (fun ω : Ω => ⟪f ω (u ω), u ω⟫) μ :=
    Real.HolderConjugate.integrable_memLp_inner_memLp hpq hwd hup
  have hnorm_integ : Integrable (‖u ·‖ ^ p) μ :=
    integrable_norm_rpow_of_memLp hp hup
  have hae : ∀ᵐ ω ∂μ, ⟪f ω (u ω), u ω⟫ ≥ C₂ * ‖u ω‖ ^ p - b ω := by
    filter_upwards [hfCpb] with ω hω
    exact hω (u ω)
  ⟨hwd, hinteg, integral_inner_ge_of_ae_inner_ge_of_integrable hinteg hb1 hnorm_integ hae⟩
end IsCaratheodory
end NemytskiiLebesgue
