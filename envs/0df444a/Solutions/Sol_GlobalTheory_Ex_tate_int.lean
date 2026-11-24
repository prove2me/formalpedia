-- Prove2me | solution 1 for GlobalTheory.Ex.tate_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T15:06:17.539058+00:00
-- url     : https://prove2.me/submissions/78eef774-461e-494b-b5a5-258f8b027ba1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Theorems.Thm_GlobalTheory_Ex_tateForm_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
attribute [instance] NumB.grp
attribute [instance] NumD.add NumD.free NumD.fin
variable {O : Type} [CommRing O]
namespace GlobalTheory.Ex
theorem _root_.solution {C : Type} [NormedField C] (q : Cˣ) (hq : ‖(q : C)‖ < 1) : (tate q).Int (tateForm q) where
  θ _ _ _ := norm_one
  σ _ := norm_one
  th _ := norm_one.le
  ψ (n : ℤ) := by
    have h0 : 0 < ‖(q : C)‖ := norm_pos_iff.2 q.ne_zero
    change ‖((q ^ n ^ 2 : Cˣ) : C)‖ = Real.exp (-tateForm q n)
    rw [tateForm_apply, Units.val_zpow_eq_zpow_val, norm_zpow, ← Real.rpow_intCast, Real.rpow_def_of_pos h0]
    congr 1
    push_cast
    ring
  pos := by
    have h0 : 0 < ‖(q : C)‖ := norm_pos_iff.2 q.ne_zero
    have hl : 0 < -Real.log ‖(q : C)‖ := neg_pos.2 (Real.log_neg h0 hq)
    have e : (tateForm q : ℤ → ℝ) = fun n : ℤ => ‖(n : ℝ)‖ ^ 2 * (-Real.log ‖(q : C)‖) :=
      funext fun n => by rw [tateForm_apply, Real.norm_eq_abs, sq_abs]
    change Filter.Tendsto (tateForm q : ℤ → ℝ) Filter.cofinite Filter.atTop
    rw [e]
    exact ((Filter.tendsto_pow_atTop two_ne_zero).comp
      ((tendsto_norm_cocompact_atTop (E := ℝ)).comp Int.tendsto_coe_cofinite)).atTop_mul_const hl
end GlobalTheory.Ex
