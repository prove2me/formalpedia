-- Prove2me | solution 1 for GlobalTheory.KroneckerLimit.tendsto_integral_part
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:50:19.053566+00:00
-- url     : https://prove2.me/submissions/4e09b802-8e82-41c8-a799-c6d55b2ea233

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_SummableAndAbsTsumSubIntegralLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Theorems.Thm_GlobalTheory_KroneckerLimit_tendsto_zeta_two_mul_sub_one
import Theorems.Thm_GlobalTheory_KroneckerLimit_betaConst_one
import Theorems.Thm_GlobalTheory_KroneckerLimit_hasDerivAt_betaConst_one


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
theorem _root_.solution {y : ℝ} (hy : 0 < y) :
    Tendsto (fun s : ℝ => 2 * (betaConst s * y ^ (1 - s)) * (∑' n : ℕ, (n + 1 : ℝ) ^ (1 - 2 * s))
      - π / (s - 1)) (𝓝[>] 1)
      (𝓝 (2 * π * (Real.eulerMascheroniConstant - Real.log 2) - π * Real.log y)) := by
  set g : ℝ → ℝ := fun s => betaConst s * y ^ (1 - s) with hg
  have hg1 : g 1 = π := by simp [hg, betaConst_one]
  have hd : HasDerivAt g (-2 * π * Real.log 2 - π * Real.log y) 1 := by
    have h1 : HasDerivAt (fun s : ℝ => y ^ (1 - s)) _ 1 :=
      ((hasDerivAt_id' (1 : ℝ)).const_sub 1).const_rpow hy
    refine (hasDerivAt_betaConst_one.mul h1).congr_deriv ?_
    simp [betaConst_one]
    ring
  have t1 : Tendsto g (𝓝[>] 1) (𝓝 π) :=
    hg1 ▸ hd.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have t2 := (hasDerivAt_iff_tendsto_slope.1 hd).mono_left
    (nhdsWithin_mono _ (show Ioi (1 : ℝ) ⊆ {1}ᶜ from fun _ h => ne_of_gt h))
  have t3 := ((t1.const_mul 2).mul tendsto_zeta_two_mul_sub_one).add t2
  convert t3.congr' ?_ using 2
  · ring
  · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
    have : s - 1 ≠ 0 := by linarith
    rw [slope_def_field, hg1]
    change _ = 2 * g s * _ - _
    field_simp
    ring
end GlobalTheory.KroneckerLimit
