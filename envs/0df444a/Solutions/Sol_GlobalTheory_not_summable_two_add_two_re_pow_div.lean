-- Prove2me | solution 1 for GlobalTheory.not_summable_two_add_two_re_pow_div
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:12:42.940875+00:00
-- url     : https://prove2.me/submissions/9e333280-f373-43de-9884-d8e639af1fb7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LandauSummableOfExpDirichletSeriesEntire
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HasSumLogZetaSqMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_EulerProductNeZeroOneOfEntire
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
theorem _root_.solution (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ¬ Summable fun k : ℕ => (2 + 2 * (c ^ (k + 1)).re) / ((k : ℝ) + 1) := by
  intro h
  set f := fun k : ℕ => (2 + 2 * (c ^ (k + 1)).re) / ((k : ℝ) + 1) with hf
  have hnn : ∀ k, 0 ≤ f k := fun k =>
    div_nonneg (by linarith [neg_one_le_re_pow_of_norm_le_one hc (k + 1)]) (by positivity)
  have hkey : ∀ k : ℕ, 3 / 2 * (1 / ((k : ℝ) + 1)) ≤ f k + f (2 * k + 1) := by
    intro k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    have hn : ‖c ^ (k + 1)‖ ^ 2 ≤ 1 := by
      rw [norm_pow]
      exact pow_le_one₀ (by positivity) (pow_le_one₀ (norm_nonneg _) hc)
    rw [Complex.sq_norm, Complex.normSq_apply] at hn
    have hz : c ^ (2 * k + 1 + 1) = c ^ (k + 1) * c ^ (k + 1) := by ring
    have hsum : f k + f (2 * k + 1) = (3 + 2 * (c ^ (k + 1)).re +
        ((c ^ (k + 1)).re * (c ^ (k + 1)).re - (c ^ (k + 1)).im * (c ^ (k + 1)).im)) /
        ((k : ℝ) + 1) := by
      simp only [hf, hz, Complex.mul_re]
      push_cast
      field_simp
      ring
    rw [hsum, mul_one_div]
    exact (div_le_div_iff_of_pos_right hk).mpr (by nlinarith [sq_nonneg ((c ^ (k + 1)).re + 1 / 2)])
  have hs2 : Summable fun k : ℕ => f k + f (2 * k + 1) :=
    h.add (h.comp_injective (fun a b hab => by simpa using hab))
  have hharm : Summable fun k : ℕ => 1 / ((k : ℝ) + 1) := by
    have h3 : Summable fun k : ℕ => 3 / 2 * (1 / ((k : ℝ) + 1)) :=
      hs2.of_nonneg_of_le (fun k => by positivity) hkey
    exact (summable_mul_left_iff (by norm_num : (3 / 2 : ℝ) ≠ 0)).mp h3
  refine Real.not_summable_one_div_natCast ((summable_nat_add_iff 1).mp ?_)
  simpa using hharm
end _root_.GlobalTheory
end GlobalTheory
