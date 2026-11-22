-- Prove2me | solution 1 for NemytskiiLebesgue.IsCaratheodory.tendsTo_eLpNorm_frechet_ratio_of_ae_tendsTo
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:39:33.019576+00:00
-- url     : https://prove2.me/submissions/c1895398-8868-4cfe-920d-74862c0ab4c4

module
public import Mathlib.Analysis.Calculus.MeanValue
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Continuity
public import Definitions.Def_LeanPool_NemytskiiLebesgue_Frechet
public import Theorems.Thm_NemytskiiLebesgue_ae_norm_frechet_ratio_tendsto_zero
public import Theorems.Thm_NemytskiiLebesgue_IsCaratheodory_aestronglyMeas_frechet_remainder
public import Theorems.Thm_NemytskiiLebesgue_ae_frechet_ratio_le_of_ae_all_growth_deriv
public import Theorems.Thm_NemytskiiLebesgue_convergesTo_of_ae_tendsTo_of_ae_norm_le
public import Theorems.Thm_NemytskiiLebesgue_memLp_norm_rpow_div_of_memLp
public import Theorems.Thm_NemytskiiLebesgue_memLp_rpow_div_of_memLp_of_ae_nonneg
public import Theorems.Thm_NemytskiiLebesgue_ne_zero_of_ge_one

section
public section
namespace NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
private lemma memLp_dominating_of_memLp_of_ea_nonneg_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {p : ℝ} (h1p : 1 ≤ p)
    {r : ℝ} (h1r : 1 ≤ r)
    {b : Ω → ℝ} (hbr : MemLp b ↱r μ)
    {m : ℕ} {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {g : Ω → ℝ} (h0g : 0 ≤ᵐ[μ] g) (hgp : MemLp g ↱p μ)
    (C : ℝ) :
    MemLp (fun ω : Ω => 2 * b ω + C * (‖u ω‖ + g ω) ^ (p / r) + C * ‖u ω‖ ^ (p / r)) ↱r μ := by
  refine MemLp.add (MemLp.add (hbr.const_mul 2) ?_) ?_
  · apply MemLp.const_mul
    convert memLp_rpow_div_of_memLp_of_ae_nonneg .. using 1
    any_goals positivity
    · rw [div_div_cancel₀ (ne_zero_of_ge_one h1p)]
    · filter_upwards [h0g] with ω hω
      exact add_nonneg (norm_nonneg _) hω
    · exact hup.norm.add hgp
  · convert (memLp_norm_rpow_div_of_memLp (show 0 < p / r by positivity) hup.norm).const_mul C
    using 1
    · norm_num
    · rw [div_div_cancel₀ (ne_zero_of_ge_one h1p)]
end NemytskiiLebesgue
end
end

set_option autoImplicit true
@[expose] public section
public section
open NemytskiiLebesgue
open scoped NemytskiiLebesgue
open MeasureTheory _root_.Filter
open scoped ENNReal Topology
namespace NemytskiiLebesgue
namespace IsCaratheodory
theorem _root_.solution
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {m k : ℕ}
    {f : Ω → ℝ^m → ℝ^k} (hf : IsCaratheodory f μ)
    {f' : Ω → ℝ^m → (ℝ^m →L[ℝ] ℝ^k)} (hf' : IsCaratheodory f' μ)
    (hff' : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, HasFDerivAt (f ω) (f' ω ξ) ξ)
    {p : ℝ} (h1p : 1 ≤ p)
    {r : ℝ} (h1r : 1 ≤ r)
    {C : ℝ} (hC : 0 < C)
    {b : Ω → ℝ} (h0b : 0 ≤ᵐ[μ] b) (hbr : MemLp b ↱r μ)
    (hf'bCpr : ∀ᵐ ω : Ω ∂μ, ∀ ξ : ℝ^m, ‖f' ω ξ‖ ≤ b ω + C * ‖ξ‖ ^ (p / r))
    {u : Ω → ℝ^m} (hup : MemLp u ↱p μ)
    {l : ℕ → Ω → ℝ^m} (hl : ∀ n : ℕ, AEStronglyMeasurable (l n) μ)
    {g : Ω → ℝ} (h0g : 0 ≤ᵐ[μ] g) (hgp : MemLp g ↱p μ)
    (hlg : ∀ᵐ ω : Ω ∂μ, ∀ n : ℕ, ‖l n ω‖ ≤ g ω)
    (hl0 : ∀ᵐ ω : Ω ∂μ, Tendsto (l · ω) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => eLpNorm
        (fun ω : Ω => ‖f ω (u ω + l n ω) - f ω (u ω) - f' ω (u ω) (l n ω)‖ / ‖l n ω‖) ↱r μ)
      atTop
      (𝓝 0) := by
  simpa [Function.NemytskiiConvergesTo, Pi.sub_def, sub_zero] using
    convergesTo_of_ae_tendsTo_of_ae_norm_le
      (b := fun ω : Ω => 2 * b ω + C * (‖u ω‖ + g ω) ^ (p / r) + C * ‖u ω‖ ^ (p / r))
      (ENNReal.ofReal_one ▸ ENNReal.ofReal_le_ofReal h1r)
      ENNReal.ofReal_ne_top
      (fun n : ℕ => by
        have remainder_meas : AEStronglyMeasurable (fun ω : Ω => f ω (u ω + l n ω) - f ω (u ω) -
          (f' ω (u ω)) (l n ω)) μ := by
          apply_rules [aestronglyMeas_frechet_remainder]
        exact remainder_meas.norm.mul ((hl n).norm.aemeasurable.inv.aestronglyMeasurable)
      )
      aestronglyMeasurable_const
      (by apply_rules [memLp_dominating_of_memLp_of_ea_nonneg_of_memLp])
      (fun n : ℕ => by
        filter_upwards [ae_frechet_ratio_le_of_ae_all_growth_deriv hf'.ae_continuous hff' hC h1p
          h1r h0b hf'bCpr h0g (hlg.mono ↓(· n)) u] with _ _
        rwa [Real.norm_of_nonneg (by positivity)]
      )
      (by
        filter_upwards [h0b, h0g] with ω hbω hgω
        simpa using add_nonneg
          (add_nonneg (mul_nonneg zero_le_two hbω) (mul_nonneg hC.le (Real.rpow_nonneg (add_nonneg
            (norm_nonneg _) hgω) _)))
          (mul_nonneg hC.le (Real.rpow_nonneg (norm_nonneg _) _))
      )
      (ae_norm_frechet_ratio_tendsto_zero hff' hl0 _)
end IsCaratheodory
end NemytskiiLebesgue
