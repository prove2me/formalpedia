-- Prove2me | solution 1 for MasulloRH.omitted_sum_zero_forall_imp_no_omitted_zeros
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:49:12.88399+00:00
-- url     : https://prove2.me/submissions/fb3c541a-fbd7-4fa1-9df0-f70945c169bd

import Theorems.Thm_MasulloRH_regularized_mellin_limit
import Theorems.Thm_MasulloRH_weighted_zero_summability
import Theorems.Thm_MasulloRH_regularized_spectral_domination_any_window
import Theorems.Thm_MasulloRH_trace_window_comparison
import Theorems.Thm_MasulloRH_regularized_test_admissible
import Theorems.Thm_MasulloRH_single_resolvent_test
import Mathlib.Analysis.Normed.Group.Tannery

open MasulloRH Set Filter
open scoped Topology

-- The cutoff limit is adapted from the accepted full-strip proof and the cutoff
-- arguments of davidloeffler (see the submission explanation for attribution).
/-- Uniform summable domination allows passage through the full zero sum. -/
private theorem spectralLimit (α : ℝ) (hα : 0 < α)
    (s : ℂ) (hs : (3 / 2 : ℝ) < s.re) :
    Tendsto (fun n : ℕ => cutoffSpectral α n s) atTop
      (𝓝 (regularizedSpectral α s)) := by
  obtain ⟨C, hC, hbound⟩ := regularized_spectral_domination_any_window α s hs
  apply tendsto_tsum_of_dominated_convergence
    ((weighted_zero_summability α hα).mul_left C)
  · intro ρ
    have hr : (ρ : ℂ).re < 1 := ρ.property.2.2.1
    have hwr : ((ρ : ℂ) - 1 / 2).re = (ρ : ℂ).re - 1 / 2 := by simp
    have hm := regularized_mellin_limit s ((ρ : ℂ) - 1 / 2)
      (by rw [hwr]; linarith) (by rw [hwr]; linarith)
    convert hm.const_mul (analyticOrderNatAt riemannZeta (ρ : ℂ) : ℂ) using 1 <;>
      simp only [zetaTraceTerm, zeroResolventTerm] <;> congr 3 <;> ring
  · exact .of_forall hbound


theorem solution (α : ℝ) (hα : 0 < α) (_hα2 : α < 1/2) :
    (∀ (φ : ℝ → ℂ), IsRationalTraceTest φ →
      (let omitted := {ρ : {z : ℂ // ConnesRZ.IsCriticalZero z} | α ≤ |ρ.val.re - 1/2|}
       (∑' r : omitted, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0)) →
    ∀ ρ : {z : ℂ // ConnesRZ.IsCriticalZero z}, |ρ.val.re - 1/2| < α := by
  intro hvan ρ
  let z : ZetaZerosInTraceStrip (1/2) := ⟨ρ.val, ρ.prop.1, ρ.prop.2.1, ρ.prop.2.2,
    abs_lt.mpr ⟨by linarith [ρ.prop.2.1], by linarith [ρ.prop.2.2]⟩⟩
  apply (single_resolvent_test α).1 _ z
  have hcut (n : ℕ) : cutoffSpectral α n 3 = cutoffSpectral (1/2) n 3 := by
    let φ := regularizedTraceTest n 3
    have hφ : IsRationalTraceTest φ := regularized_test_admissible _ _
    let omitted (b : ℝ) := {r : {w : ℂ // ConnesRZ.IsCriticalZero w} | b ≤ |r.val.re - 1/2|}
    have : IsEmpty (omitted (1/2)) := ⟨fun r => by
      have hz := r.val.prop
      have hr : (1/2 : ℝ) ≤ |r.val.val.re-1/2| := r.prop
      exact (not_lt_of_ge hr) (abs_lt.mpr ⟨by linarith [hz.2.1],by linarith [hz.2.2]⟩)⟩
    have hb := (trace_window_comparison α φ hφ).2.2.2.2
    have hf := (trace_window_comparison (1/2) φ hφ).2.2.2.2
    change _ + cutoffSpectral α n 3 + (∑' r : omitted α, _) = _ at hb
    change _ + cutoffSpectral (1/2) n 3 + (∑' r : omitted (1/2), _) = _ at hf
    have hzero : (∑' r : omitted α, (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := hvan φ hφ
    rw [hzero, add_zero] at hb
    have hfull : (∑' r : omitted (1/2), (ConnesRZ.zeroMult r.val.val : ℂ) * mellin φ (r.val.val - 1/2)) = 0 := tsum_empty
    rw [hfull, add_zero] at hf
    exact add_left_cancel (hb.trans hf.symm)
  have heq := tendsto_nhds_unique (spectralLimit α hα 3 (by norm_num))
    ((spectralLimit (1/2) (by norm_num) 3 (by norm_num)).congr (fun n => (hcut n).symm))
  simp only [regularizedTraceRHS, heq, le_refl]
