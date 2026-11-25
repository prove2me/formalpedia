-- Prove2me | solution 1 for GlobalTheory.ActionGauge.exists_action_gauge
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:20:44.315828+00:00
-- url     : https://prove2.me/submissions/8f61c01f-a6ab-47cc-8e98-1b5c43c4cf27

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_CalcExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsActionGauge
import Theorems.Thm_GlobalTheory_ActionGauge_left_right_commute
import Theorems.Thm_GlobalTheory_ActionGauge_expS_logAd
import Theorems.Thm_GlobalTheory_ActionGauge_logAd_mem
import Theorems.Thm_GlobalTheory_ActionGauge_logAd_add
import Theorems.Thm_GlobalTheory_ActionGauge_logAd_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gp_pt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
open GlobalTheory GlobalTheory.ActionGauge
namespace GlobalTheory.ActionGauge
theorem _root_.solution :
    (∀ (O : Type) [CommRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (V : Type) [AddCommGroup V] [Module ℚ V] (l r : O →+* Module.End ℚ V), (∀ a b, Commute (l a) (r b)) → ∀ δ : O →+ V, (∀ a b, δ (a * b) = l b (δ a) + r a (δ b)) → ∃ v : V, ∀ a, δ a = l a v - r a v) → ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] [Module.Free ℤ O] [Module.Finite ℤ O] [IsReduced O] (B : FB k d O), B.ph1 = 1 → B.ph2 = 1 → ∃ h : PS k 2 d, (ev (n := 1) ![0, pt k d 0] h = 0 ∧ ev (n := 1) ![pt k d 0, 0] h = 0) ∧ (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h - ev (n := 3) ![addOf B.G.F (pt k d 0) (pt k d 1), pt k d 2] h) = 0 ∧ (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h - ev (n := 3) ![pt k d 0, addOf B.G.F (pt k d 1) (pt k d 2)] h) = 0 ∧ ∀ a : O, B.ad a = FB.expS k (ev (n := 2) ![comp1 (B.A.act a) (pt k d 0), pt k d 1] h - ev (n := 2) ![pt k d 0, comp1 (B.A.act (star a)) (pt k d 1)] h) := by
  intro H k _ _ d O _ _ _ _ _ B h1 h2
  let δ : O →+ biadd B.G := AddMonoidHom.mk' (fun a => ⟨logAd B a, logAd_mem B h1 h2 a⟩)
    (fun a b => Subtype.ext (logAd_add B h1 h2 a b))
  obtain ⟨v, hv⟩ := H O (biadd B.G) (leftHom B.A) ((rightHom B.A).comp (starRingEnd O))
    (fun a b => left_right_commute B.A a (star b)) δ (fun a b => Subtype.ext (logAd_mul B a b))
  refine ⟨v, ⟨v.2.1 _ _ (gp_pt 0), v.2.2.1 _ _ (gp_pt 0)⟩, ?_, ?_, fun a => ?_⟩
  · rw [v.2.2.2.1 _ _ _ _ (gp_pt 0) (gp_pt 1) (gp_pt 2), sub_self]
  · rw [v.2.2.2.2 _ _ _ _ (gp_pt 0) (gp_pt 1) (gp_pt 2), sub_self]
  · rw [← expS_logAd B a]
    exact congrArg (FB.expS k) (congrArg Subtype.val (hv a))
end GlobalTheory.ActionGauge
