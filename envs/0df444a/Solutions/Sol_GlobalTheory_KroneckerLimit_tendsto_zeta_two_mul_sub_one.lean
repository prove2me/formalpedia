-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.tendsto_zeta_two_mul_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:33:48.786298+00:00
-- url     : https://prove2.me/submissions/48e3a3a0-6b02-4a15-9064-7137aab41287

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology MeasureTheory Set
open scoped Real
open GlobalTheory GlobalTheory.KroneckerLimit
namespace GlobalTheory.KroneckerLimit
theorem _root_.solution :
    Tendsto (fun s : ℝ => (∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s)) - 1 / (2 * (s - 1))) (𝓝[>] 1)
      (𝓝 Real.eulerMascheroniConstant) := by
  have h0 : Tendsto (fun s : ℝ => 2 * s - 1) (𝓝[>] 1) (𝓝[>] 1) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Continuous fun s : ℝ => 2 * s - 1 := by fun_prop
      have := (this.tendsto 1).mono_left (nhdsWithin_le_nhds (s := Ioi 1))
      norm_num at this
      exact this
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      show 1 < 2 * s - 1
      linarith
  have h1 := (Complex.continuous_re.tendsto _).comp
    (ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right.comp h0)
  rw [Complex.ofReal_re] at h1
  refine h1.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  simp only [Function.comp_apply]
  refine (congrArg Complex.re ?_).trans (Complex.ofReal_re _)
  rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by rw [Complex.ofReal_re]; linarith),
    Complex.ofReal_sub (∑' _, _), Complex.ofReal_tsum]
  congr 1
  · congr 1 with n
    rw [Complex.ofReal_cpow (by positivity), one_div, ← Complex.cpow_neg]
    congr 1 <;> push_cast <;> ring
  · push_cast
    congr 1
    ring
end GlobalTheory.KroneckerLimit
