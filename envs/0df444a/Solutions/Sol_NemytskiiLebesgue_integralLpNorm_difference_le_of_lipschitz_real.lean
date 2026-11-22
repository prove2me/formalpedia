-- Prove2me | solution 1 for NemytskiiLebesgue.integralLpNorm_difference_le_of_lipschitz_real
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:39.467702+00:00
-- url     : https://prove2.me/submissions/e18c0b7c-749f-47f2-ad31-25ae44a74b28

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_difference_le_of_lipschitz

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory
open scoped NNReal ENNReal
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k}
    {L : Ω → ℝ} (hL : AEMeasurable L μ)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : ℝ^m, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖)
    {p : ℝ≥0∞}
    {u : Ω → ℝ^m} (hup : MemLp u p μ)
    {v : Ω → ℝ^m} (hvp : MemLp v p μ) :
    integralLpNorm (fun ω : Ω => f ω (u ω) - f ω (v ω)) p μ ≤ eLpNorm L ⊤ μ * eLpNorm (u - v) p μ :=
  integralLpNorm_difference_le_of_lipschitz hL.aestronglyMeasurable hfL
    (hup.aestronglyMeasurable.sub hvp.aestronglyMeasurable) p
end NemytskiiLebesgue
