-- Prove2me | solution 1 for GlobalTheory.CanonGaugeAssembly.Cob.chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:04:58.335818+00:00
-- url     : https://prove2.me/submissions/8a9d8d86-def9-4677-8348-175e6414ff78

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_CanonGaugeOfSteps
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add


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
open GlobalTheory GlobalTheory.CanonGaugeAssembly
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.CanonGaugeAssembly
namespace Cob
theorem _root_.solution [Algebra ℚ k] {n : ℕ} {c : PS k 2 d → PS k n d} (hc : Cob c)
    {h₁ h₂ h₃ h₄ : PS k 2 d} (c₁ : constantCoeff h₁ = 0) (c₂ : constantCoeff h₂ = 0)
    (c₃ : constantCoeff h₃ = 0) (c₄ : constantCoeff h₄ = 0) {p₀ p₁ p₂ p₃ : PS k n d}
    (e₁ : p₀ = p₁ * FB.expS k (c h₁)) (e₂ : p₁ = p₂ * FB.expS k (c h₂))
    (e₃ : p₂ = p₃ * FB.expS k (c h₃)) (e₄ : p₃ = FB.expS k (c h₄)) :
    p₀ = FB.expS k (c (h₁ + h₂ + h₃ + h₄)) := by
  have k₁ := hc.const _ c₁
  have k₂ := hc.const _ c₂
  have k₃ := hc.const _ c₃
  have k₄ := hc.const _ c₄
  rw [hc.add, hc.add, hc.add, gt_expS_add _ _ (by simp [k₁, k₂, k₃]) k₄,
    gt_expS_add _ _ (by simp [k₁, k₂]) k₃, gt_expS_add _ _ k₁ k₂, e₁, e₂, e₃, e₄]
  ring
end Cob
end GlobalTheory.CanonGaugeAssembly
