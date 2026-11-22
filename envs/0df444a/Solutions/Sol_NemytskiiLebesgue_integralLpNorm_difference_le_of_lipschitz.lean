-- Prove2me | solution 1 for NemytskiiLebesgue.integralLpNorm_difference_le_of_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:24.942183+00:00
-- url     : https://prove2.me/submissions/9d3a2570-356e-41d8-a71c-1fa71d86f098

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_le_eLpNorm_of_ae_le


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {D : Type*} [NormedAddCommGroup D]
    {F : Type*} [NormedAddCommGroup F]
    {f : Ω → D → F}
    {L : Ω → ℝ} (hL : AEStronglyMeasurable L μ)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : D, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖)
    {u v : Ω → D} (huv : AEStronglyMeasurable (u - v) μ)
    (p : ℝ≥0∞) :
    integralLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) p μ ≤ eLpNorm L ⊤ μ * eLpNorm (u - v) p μ
      := by
  calc integralLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) p μ
    ≤ eLpNorm (L • fun ω : Ω => ‖u ω - v ω‖) p μ := by
        apply integralLpNorm_le_eLpNorm_of_ae_le (hL.smul huv.norm)
        filter_upwards [hfL] with ω hω
        change ‖f ω (u ω) - f ω (v ω)‖ ≤ ‖(L • fun ω : Ω => ‖u ω - v ω‖) ω‖
        exact le_trans (hω _ _) (le_abs_self _)
  _ ≤ eLpNorm L ⊤ μ * eLpNorm (fun ω : Ω => ‖u ω - v ω‖) p μ :=
        eLpNorm_smul_le_mul_eLpNorm huv.norm hL
  _ = eLpNorm L ⊤ μ * eLpNorm (u - v) p μ := by
        congr 1
        exact eLpNorm_norm (u - v)
end NemytskiiLebesgue
