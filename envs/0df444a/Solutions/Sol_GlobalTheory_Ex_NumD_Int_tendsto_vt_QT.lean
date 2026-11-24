-- Prove2me | solution 1 for GlobalTheory.Ex.NumD.Int.tendsto_vt_QT
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T15:08:00.504485+00:00
-- url     : https://prove2.me/submissions/23b5a03e-f03f-40bd-8098-0c88cc546777

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_NormRepGeneratorsAndThetaSeriesTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SummableVtQT
import Theorems.Thm_GlobalTheory_Ex_NumD_Int_norm_vt_QT_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.NumD GlobalTheory.Ex.NumD.Int
variable {C : Type} [NormedField C] {N : NumD C} {q : QuadraticMap ℤ N.X ℝ}
namespace GlobalTheory.Ex.NumD.Int
theorem _root_.solution (h : N.Int q) {k : ℕ} (hk : k ≠ 0) (p : N.QT k) :
    Filter.Tendsto (N.vt p.1.2) Filter.cofinite (nhds 0) := by
  have inj : Function.Injective fun χ : N.X => p.1.1.toAdd + k • χ := fun a b e => by
    have e' : k • a = k • b := add_left_cancel e
    rw [← natCast_zsmul, ← natCast_zsmul] at e'
    exact smul_right_injective N.X (Int.natCast_ne_zero.2 hk) e'
  have t₁ := h.pos.comp inj.tendsto_cofinite
  have kp : (0 : ℝ) < (k : ℝ) ^ 2 := pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero hk)) 2
  have t₂ := (Filter.tendsto_atTop_add_const_right _ (-q p.1.1.toAdd) t₁).atTop_div_const kp
  have t₃ := Real.tendsto_exp_neg_atTop_nhds_zero.comp t₂
  refine squeeze_zero_norm (h.norm_vt_QT_le hk p) ?_
  simpa only [Function.comp_def, sub_eq_add_neg] using t₃
end GlobalTheory.Ex.NumD.Int
