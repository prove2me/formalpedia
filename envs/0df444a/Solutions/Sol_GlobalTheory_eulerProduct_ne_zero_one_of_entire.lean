-- Prove2me | solution 1 for GlobalTheory.eulerProduct_ne_zero_one_of_entire
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:56:36.803708+00:00
-- url     : https://prove2.me/submissions/db22d09d-5ca2-41e5-b1c0-28ead56c1e58

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
import Theorems.Thm_GlobalTheory_not_summable_two_add_two_re_pow_div
import Theorems.Thm_GlobalTheory_conj_neg_log_euler_factor
import Theorems.Thm_GlobalTheory_LogEulerSeries_hasSum_log_zeta_sq_mul
import Theorems.Thm_GlobalTheory_landau_exp_summable

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in
private lemma neg_one_le_re_pow_of_norm_le_one {c : ℂ} (hc : ‖c‖ ≤ 1) (k : ℕ) : -1 ≤ (c ^ k).re := by
  have h1 : ‖c ^ k‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hc
  have h2 := Complex.abs_re_le_norm (c ^ k)
  linarith [(abs_le.mp (h2.trans h1)).1]
end GlobalTheory
end

set_option autoImplicit false
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
open GlobalTheory
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (ι : Type) (N : ι → ℕ) (c : ι → ℂ), (∀ i, 2 ≤ N i) → (∀ i, ‖c i‖ ≤ 1) → (∀ σ : ℝ, 1 < σ → Summable fun i => (N i : ℝ) ^ (-σ)) → Nonempty ι → ∀ Z L : ℂ → ℂ, Differentiable ℂ Z → Differentiable ℂ L → (∀ s : ℂ, 1 < s.re → Z s = (s - 1) * Complex.exp (∑' i, -Complex.log (1 - 1 * ((N i : ℕ) : ℂ) ^ (-s)))) → (∀ s : ℂ, 1 < s.re → L s = Complex.exp (∑' i, -Complex.log (1 - c i * ((N i : ℕ) : ℂ) ^ (-s)))) → L 1 ≠ 0 := by
  intro ι N c hN hc hsum hne Z L hZ hL hZs hLs h1
  set L' : ℂ → ℂ := fun s => starRingEnd ℂ (L (starRingEnd ℂ s)) with hL'
  have hdL' : Differentiable ℂ L' := fun s => by
    have := (hL (starRingEnd ℂ s)).conj_conj
    simpa [hL', Function.comp_def] using this
  have hL'1 : L' 1 = 0 := by simp [hL', h1]
  have hds : ∀ f : ℂ → ℂ, Differentiable ℂ f → Differentiable ℂ (dslope f 1) := fun f hf =>
    differentiableOn_univ.mp ((differentiableOn_dslope Filter.univ_mem).mpr hf.differentiableOn)
  have ha : ∀ p : ι × ℕ, 0 ≤ (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1) := fun p =>
    div_nonneg (by linarith [neg_one_le_re_pow_of_norm_le_one (hc p.1) (p.2 + 1)]) (by positivity)
  have key := _root_.GlobalTheory.landau_exp_summable (ι × ℕ)
    (fun p => (2 + 2 * (c p.1 ^ (p.2 + 1)).re) / ((p.2 : ℝ) + 1))
    (fun p => ((p.2 : ℝ) + 1) * Real.log (N p.1))
    (fun s => Z s ^ 2 * dslope L 1 s * dslope L' 1 s) ha
    (fun p => mul_nonneg (by positivity)
      (Real.log_nonneg (by exact_mod_cast (by have := hN p.1; omega : 1 ≤ N p.1))))
    (((hZ.pow 2).mul (hds L hL)).mul (hds L' hdL')) (by
      intro s hs
      refine ⟨_, _root_.GlobalTheory.LogEulerSeries.hasSum_log_zeta_sq_mul ι N c hN hc hsum s hs, ?_⟩
      have hs1 : s ≠ 1 := fun h => by rw [h] at hs; simp at hs
      have hsub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
      have hL's : L' s = Complex.exp (∑' i, -Complex.log
          (1 - starRingEnd ℂ (c i) * ((N i : ℕ) : ℂ) ^ (-s))) := by
        simp only [hL']
        rw [hLs _ (by simpa using hs), ← Complex.exp_conj, Complex.conj_tsum]
        congr 1
        exact tsum_congr fun i => _root_.GlobalTheory.conj_neg_log_euler_factor (N i) (hN i) (c i) (hc i) s hs
      simp only [dslope_of_ne _ hs1, slope_def_field, h1, hL'1, sub_zero]
      rw [hZs s hs, hLs s hs, hL's, two_mul, Complex.exp_add, Complex.exp_add, Complex.exp_add]
      field_simp)
  obtain ⟨i⟩ := hne
  exact _root_.GlobalTheory.not_summable_two_add_two_re_pow_div (c i) (hc i)
    (((summable_prod_of_nonneg (fun p => ha p)).mp key).1 i)
end _root_.GlobalTheory
end GlobalTheory
