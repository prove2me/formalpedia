-- Prove2me | solution 1 for NemytskiiLebesgue.memLp_nemytskii_of_globally_lipschitz_of_aestronglyMeas
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:37:18.746293+00:00
-- url     : https://prove2.me/submissions/a134b65b-6547-47de-aaef-1946db99fa83

module
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Lipschitz

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
    {p : ℝ≥0∞}
    {f : Ω → D → F} (hf0p : MemLp (f · 0) p μ)
    {u : Ω → D} (hup : MemLp u p μ)
    (hfu : AEStronglyMeasurable ((fun ω : Ω => f ω (u ω))) μ)
    {L : Ω → ℝ} (hL' : eLpNorm L ⊤ μ < ⊤)
    (hfL : ∀ᵐ ω : Ω ∂μ, ∀ ξ η : D, ‖f ω ξ - f ω η‖ ≤ L ω * ‖ξ - η‖) :
    MemLp (fun ω : Ω => f ω (u ω)) p μ := by
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp
    (show eLpNormEssSup L μ < ⊤ from hL')
  have bound_mem : MemLp (fun ω => ‖f ω 0‖ + (C : ℝ) * ‖u ω‖) p μ :=
    hf0p.norm.add (hup.norm.const_mul (C : ℝ))
  refine ⟨hfu, (eLpNorm_mono_ae ?_).trans_lt bound_mem.eLpNorm_lt_top⟩
  filter_upwards [hfL, hC] with ω hω hCω
  have hLC : L ω ≤ (C : ℝ) := le_trans (le_abs_self _) (by exact_mod_cast hCω)
  have bound := hω (u ω) 0
  simp only [sub_zero] at bound
  have bound' := bound.trans (mul_le_mul_of_nonneg_right hLC (norm_nonneg _))
  simpa only [Real.norm_eq_abs] using
    (show ‖f ω (u ω)‖ ≤ |‖f ω 0‖ + (C : ℝ) * ‖u ω‖| by
      linarith [norm_sub_norm_le (f ω (u ω)) (f ω 0),
        le_abs_self (‖f ω 0‖ + (C : ℝ) * ‖u ω‖)])
end NemytskiiLebesgue
