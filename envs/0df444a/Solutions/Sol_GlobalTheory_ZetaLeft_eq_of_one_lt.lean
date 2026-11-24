-- Prove2me | solution 1 for GlobalTheory.ZetaLeft.eq_of_one_lt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:40:10.757209+00:00
-- url     : https://prove2.me/submissions/091db7d9-3b66-4cb4-ae02-468e9f6647a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Theorems.Thm_GlobalTheory_ZetaLeft_norm_emE_le
import Theorems.Thm_GlobalTheory_ZetaLeft_summable_nine_pow_mul_inv_sq_succ
import Theorems.Thm_GlobalTheory_ZetaLeft_tendsto_cpow_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open GlobalTheory GlobalTheory.ZetaLeft
namespace GlobalTheory.ZetaLeft
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) :
    (s - 1) * riemannZeta s = emT 1 s + ∑' n : ℕ, emE ((n : ℝ) + 1) s := by
  have hsum : Summable (fun n : ℕ => emE ((n : ℝ) + 1) s) :=
    Summable.of_norm_bounded (summable_nine_pow_mul_inv_sq_succ.mul_left ((‖s‖ + 2) ^ 4))
      (fun n => norm_emE_le (by simp) (by linarith))
  have hT : Tendsto (fun n : ℕ => emT ((n : ℝ) + 1) s) atTop (𝓝 0) := by
    have := ((tendsto_cpow_zero (c := 1 - s) (by simp; linarith)).sub
      (((tendsto_cpow_zero (c := 1 - s - 1) (by simp; linarith)).const_mul (1 - s)).div_const 2)).add
      (((tendsto_cpow_zero (c := 1 - s - 1 - 1) (by simp; linarith)).const_mul
        ((1 - s) * (1 - s - 1))).div_const 12)
    simpa [emT] using this
  have hz : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s) (riemannZeta s) := by
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow hs]
    have := (summable_nat_add_iff 1).2 (Complex.summable_one_div_nat_cpow.2 hs)
    exact (by simpa using this : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ s)).hasSum
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, emE ((n : ℝ) + 1) s =
      emT ((N : ℝ) + 1) s - emT 1 s + (s - 1) * ∑ n ∈ Finset.range N, 1 / ((n : ℂ) + 1) ^ s := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih, emE]
      have : (1 - s - 1) = -s := by ring
      rw [this, Complex.cpow_neg]
      push_cast
      ring
  have h1 := (hT.sub_const (emT 1 s)).add (hz.tendsto_sum_nat.const_mul (s - 1))
  have h2 := hsum.hasSum.tendsto_sum_nat
  simp only [hpart] at h2
  rw [tendsto_nhds_unique h2 h1]
  ring
end GlobalTheory.ZetaLeft
