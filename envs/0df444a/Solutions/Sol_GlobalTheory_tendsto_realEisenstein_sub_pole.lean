-- Prove2me | solution 1 for GlobalTheory.tendsto_realEisenstein_sub_pole
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:36:54.105074+00:00
-- url     : https://prove2.me/submissions/d628be43-0ad4-46bc-ad9a-b6f71751d702

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_tendsto_integral_part
import Theorems.Thm_GlobalTheory_KroneckerLimit_tendsto_zero_row
import Theorems.Thm_GlobalTheory_KroneckerLimit_tendsto_tsum_rowError
import Theorems.Thm_GlobalTheory_KroneckerLimit_tsum_rowError_one
import Theorems.Thm_GlobalTheory_KroneckerLimit_log_norm_eta_sq
import Theorems.Thm_GlobalTheory_KroneckerLimit_hasSum_eisenstein

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
open GlobalTheory
open KroneckerLimit
namespace GlobalTheory
theorem _root_.solution (τ : UpperHalfPlane) :
    Tendsto (fun s : ℝ =>
        (∑' p : {p : ℤ × ℤ // p ≠ 0}, τ.im ^ s / ‖(p.1.1 * τ + p.1.2 : ℂ)‖ ^ (2 * s))
          - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log τ.im
        - 2 * π * Real.log (‖ModularForm.eta τ‖ ^ 2))) := by
  have hy := τ.im_pos
  have t0 : Tendsto (fun s : ℝ => τ.im ^ s) (𝓝[>] 1) (𝓝 τ.im) := by
    simpa using (Real.continuousAt_const_rpow (b := 1) hy.ne').tendsto.mono_left
      (nhdsWithin_le_nhds (s := Ioi 1))
  have t1 := (t0.mul (tendsto_zero_row.add ((tendsto_tsum_rowError τ.re hy).const_mul 2))).add
    (tendsto_integral_part hy)
  have e1 := tsum_rowError_one τ hy
  have e2 := log_norm_eta_sq τ hy
  rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at e1
  rw [UpperHalfPlane.coe_im] at e2
  convert t1.congr' ?_ using 2
  · rw [e1, e2]
    field_simp
    ring
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    rw [(hasSum_eisenstein τ hs).tsum_eq]
    ring
end GlobalTheory
