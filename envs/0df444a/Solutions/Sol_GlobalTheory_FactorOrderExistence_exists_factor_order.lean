-- Prove2me | solution 1 for GlobalTheory.FactorOrderExistence.exists_factor_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T14:51:16.748814+00:00
-- url     : https://prove2.me/submissions/1aab8f41-a4e2-460f-bd63-74e4546f5c24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsFactorOrder

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.FactorOrderExistence
open Filter Topology
namespace GlobalTheory.FactorOrderExistence
theorem _root_.solution {U : Set ℂ} {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g U) {w : ℂ}
    (hw : w ∈ U) (hord : analyticOrderAt g w ≠ ⊤) :
    ∃ h : ℂ → ℂ, AnalyticOnNhd ℂ h U ∧
      (∀ z : ℂ, g z = (z - w) ^ analyticOrderNatAt g w * h z) ∧ h w ≠ (0 : ℂ) := by
  classical
  obtain ⟨h0, h0a, h0ne, hev⟩ := ((hg w hw).analyticOrderAt_ne_top).1 hord
  set n := analyticOrderNatAt g w with hn
  refine ⟨fun z => if z = w then h0 w else g z / (z - w) ^ n, ?_, ?_, ?_⟩
  · intro z hz
    by_cases hzw : z = w
    · subst hzw
      refine h0a.congr ?_
      filter_upwards [hev] with y hy
      by_cases hyz : y = z
      · simp [hyz]
      · have hne : (y - z) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hyz)
        simp only [hyz, if_false]
        rw [hy, smul_eq_mul, mul_div_cancel_left₀ _ hne]
    · have ha : AnalyticAt ℂ (fun y => g y / (y - w) ^ n) z :=
        (hg z hz).div ((analyticAt_id.sub analyticAt_const).pow n)
          (pow_ne_zero _ (sub_ne_zero.2 hzw))
      refine ha.congr ?_
      filter_upwards [isOpen_ne.mem_nhds hzw] with y hy
      simp [hy]
  · intro z
    by_cases hzw : z = w
    · subst hzw
      have := hev.self_of_nhds
      simpa using this
    · have hne : (z - w) ^ n ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hzw)
      simp only [hzw, if_false]
      field_simp
  · simpa using h0ne
end GlobalTheory.FactorOrderExistence
