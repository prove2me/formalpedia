-- Prove2me | solution 1 for GlobalTheory.tendsto_sub_mul_weierstrassZeta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:43:21.749886+00:00
-- url     : https://prove2.me/submissions/d9bc5af7-0a20-45a0-9dff-4310230760b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_HasSumLocallyUniformlyWeierstrassZetaExcept

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Filter Complex PeriodPair
open scoped Topology ComplexConjugate Real
open GlobalTheory
variable (L : PeriodPair)
namespace GlobalTheory
theorem _root_.solution {x : ℂ} (hx : x ∈ L.lattice) :
    Tendsto (fun z => (z - x) * weierstrassZeta L z) (𝓝[≠] x) (𝓝 1) := by
  have hc : ContinuousAt (fun z => (z - x) * (weierstrassZetaExcept L x z + (1 / x + z / x ^ 2)) + 1)
      x := by
    have := (analyticAt_weierstrassZetaExcept L x).continuousAt
    fun_prop
  have h := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := {x}ᶜ))
  simp only [sub_self, zero_mul, zero_add] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with z hz
  have : z - x ≠ 0 := sub_ne_zero.2 hz
  rw [← weierstrassZetaExcept_add L hx, zetaTerm_eq]
  have : (z - x) * (1 / (z - x)) = 1 := by field_simp
  linear_combination -this
end GlobalTheory
