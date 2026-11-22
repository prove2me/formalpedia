-- Prove2me | solution 1 for NemytskiiLebesgue.ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:11.057399+00:00
-- url     : https://prove2.me/submissions/d9d3b85f-6464-46f3-bdb6-5cb393c8da07

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali
public import Theorems.Thm_NemytskiiLebesgue_ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {k : ℕ}
    {f : Ω → ℝ^k → ℝ^k} {p : ℝ} {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hfCp : ∀ᵐ ω ∂μ, ∀ ξ η : ℝ^k, ⟪f ω ξ - f ω η, ξ - η⟫ ≥ C₂ * ‖ξ - η‖ ^ p)
    {u v : Ω → ℝ^k} (huv : (fun ω : Ω => f ω (u ω)) =ᵐ[μ] (fun ω : Ω => f ω (v ω))) :
    u =ᵐ[μ] v :=
  ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge hC₂ hfCp huv
end NemytskiiLebesgue
