-- Prove2me | solution 1 for NemytskiiLebesgue.ae_eq_of_ae_nemytskii_eq_nemytskii_of_ae_all_sub_inner_sub_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:14.87831+00:00
-- url     : https://prove2.me/submissions/5a301659-3e00-41c5-9f52-5144b8c4bcf0

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Nemytskii
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Vitali

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped NNReal ENNReal RealInnerProductSpace Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {f : Ω → E → E} {p : ℝ} {C₂ : ℝ} (hC₂ : 0 < C₂)
    (hfCp : ∀ᵐ ω ∂μ, ∀ ξ η : E, ⟪f ω ξ - f ω η, ξ - η⟫ ≥ C₂ * ‖ξ - η‖ ^ p)
    {u v : Ω → E} (huv : (fun ω : Ω => f ω (u ω)) =ᵐ[μ] (fun ω : Ω => f ω (v ω))) :
    u =ᵐ[μ] v := by
  have norm_zero : ∀ᵐ ω ∂μ, ‖u ω - v ω‖ ^ p ≤ 0 := by
    filter_upwards [hfCp, huv] with ω hω₁ hω₂
    contrapose! hω₁
    exact ⟨u ω, v ω, by simpa [hω₂] using mul_pos hC₂ hω₁⟩
  filter_upwards [norm_zero] with ω hω
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  contrapose! hω
  positivity
end NemytskiiLebesgue
