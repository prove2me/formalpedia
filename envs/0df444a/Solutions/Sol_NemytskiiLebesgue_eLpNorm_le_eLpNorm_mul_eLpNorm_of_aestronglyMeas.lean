-- Prove2me | solution 1 for NemytskiiLebesgue.eLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:38:06.566187+00:00
-- url     : https://prove2.me/submissions/6d308cc2-4a1f-4420-a05a-de7efb5979aa

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_eq_eLpNorm


set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
namespace NemytskiiLebesgue
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ} {p q r : ℝ} (hrpq : Real.HolderTriple r p q)
    {l : Ω → ℝ^m} (hl : AEStronglyMeasurable l μ)
    {ψ : Ω → ℝ} (hψ : AEStronglyMeasurable ψ μ)
    {R : Ω → ℝ^k} (hR : AEStronglyMeasurable R μ)
    (hRψl : ∀ᵐ ω : Ω ∂μ, ‖R ω‖ ≤ ψ ω * ‖l ω‖) :
    eLpNorm R ↱q μ ≤ eLpNorm ψ ↱r μ * eLpNorm l ↱p μ := by
  rw [← integralLpNorm_eq_eLpNorm hR]
  exact integralLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas hrpq hl hψ hRψl
end NemytskiiLebesgue
