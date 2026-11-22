-- Prove2me | solution 1 for NemytskiiLebesgue.convergesTo_of_ae_tendsTo_of_ae_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:17.768814+00:00
-- url     : https://prove2.me/submissions/3c533fd2-173a-4d6e-902e-418bfaef30a6

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Theorems.Thm_NemytskiiLebesgue_convergesTo_of_tendsTo_of_growth_of_aestronglyMeas


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
    {E : Type*} [NormedAddCommGroup E]
    {p : ℝ≥0∞} (hp1 : 1 ≤ p) (hp : p ≠ ⊤)
    {F : ℕ → Ω → E} (hF : ∀ n : ℕ, AEStronglyMeasurable (F n) μ)
    {g : Ω → E} (hg : AEStronglyMeasurable g μ)
    {b : Ω → ℝ} (hbp : MemLp b p μ)
    (hFb : ∀ n : ℕ, ∀ᵐ ω : Ω ∂μ, ‖F n ω‖ ≤ b ω)
    (hgb : ∀ᵐ ω : Ω ∂μ, ‖g ω‖ ≤ b ω)
    (hFg : ∀ᵐ ω : Ω ∂μ, Tendsto (F · ω) atTop (𝓝 (g ω))) :
    F.NemytskiiConvergesTo g p μ := by
  exact convergesTo_of_tendsTo_of_growth_of_aestronglyMeas hp1 hp hF
    ⟨hg, (eLpNorm_mono_ae (hgb.mono fun _ h => h.trans (le_abs_self _))).trans_lt hbp.eLpNorm_lt_top⟩
    hbp hFb hFg
end NemytskiiLebesgue
