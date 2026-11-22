-- Prove2me | solution 1 for NemytskiiLebesgue.integralLpNorm_le_eLpNorm_mul_eLpNorm_of_aestronglyMeas
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:17.302677+00:00
-- url     : https://prove2.me/submissions/8c97862e-afdd-461c-a634-578c498def54

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Theorems.Thm_NemytskiiLebesgue_integralLpNorm_le_eLpNorm_of_ae_le


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
    {R : Ω → ℝ^k} (hRψl : ∀ᵐ ω : Ω ∂μ, ‖R ω‖ ≤ ψ ω * ‖l ω‖) :
    integralLpNorm R ↱q μ ≤ eLpNorm ψ ↱r μ * eLpNorm l ↱p μ := by
  let := Real.HolderTriple.ennrealOfReal hrpq
  refine (integralLpNorm_le_eLpNorm_of_ae_le (hψ.mul hl.norm) ?_).trans ?_
  · exact hRψl.mono fun ω hω => hω.trans (le_abs_self _)
  · simpa only [Pi.smul_def, smul_eq_mul, eLpNorm_norm l] using
      (eLpNorm_smul_le_mul_eLpNorm (p := ↱r) (q := ↱p) (r := ↱q) hl.norm hψ)
end NemytskiiLebesgue
