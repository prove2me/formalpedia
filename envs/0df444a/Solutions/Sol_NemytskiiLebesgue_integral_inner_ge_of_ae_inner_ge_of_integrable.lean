-- Prove2me | solution 1 for NemytskiiLebesgue.integral_inner_ge_of_ae_inner_ge_of_integrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:36:06.637114+00:00
-- url     : https://prove2.me/submissions/ee61d923-fc5f-44b8-b1d8-31024cc101e8

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
    {k : ℕ}
    {g u : Ω → ℝ^k} (hgu : Integrable (fun ω : Ω => ⟪g ω, u ω⟫) μ)
    {b : Ω → ℝ} (hb : Integrable b μ)
    {p : ℝ} (hup : Integrable (‖u ·‖ ^ p) μ)
    {C : ℝ} (hguCupb : ∀ᵐ ω ∂μ, ⟪g ω, u ω⟫ ≥ C * ‖u ω‖ ^ p - b ω) :
    ∫ ω : Ω, ⟪g ω, u ω⟫ ∂μ ≥ C * ∫ ω : Ω, ‖u ω‖ ^ p ∂μ - ∫ ω : Ω, |b ω| ∂μ := by
  have integral_mono : ∫ ω : Ω, ⟪g ω, u ω⟫ ∂μ ≥ ∫ ω : Ω, (C * ‖u ω‖ ^ p - b ω) ∂μ := by
    apply_rules [integral_mono_ae]
    exact Integrable.sub (Integrable.const_mul hup C) hb
  rw [integral_sub (Integrable.const_mul hup _) hb, integral_const_mul] at integral_mono
  exact le_trans (sub_le_sub_left (le_of_abs_le (norm_integral_le_integral_norm b)) _) integral_mono
end NemytskiiLebesgue
