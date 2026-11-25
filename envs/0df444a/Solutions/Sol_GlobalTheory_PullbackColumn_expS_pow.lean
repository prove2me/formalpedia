-- Prove2me | solution 1 for GlobalTheory.PullbackColumn.expS_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:04:22.039898+00:00
-- url     : https://prove2.me/submissions/8f9963ef-a0ef-4f83-b7d8-1f5641b08bbe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_NabTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantDerivAlongEndo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_NabValPullbackMonomial
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_gt_expS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_const_smul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_WickVanishing_nt_expS_zero


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
open GlobalTheory GlobalTheory.PullbackColumn
variable {k : Type} [CommRing k] {d : ℕ}
namespace GlobalTheory.PullbackColumn
theorem _root_.solution [Algebra ℚ k] {n : ℕ} (g : PS k n d) (hg : constantCoeff g = 0) (m : ℕ) :
    FB.expS k g ^ m = FB.expS k ((m : k) • g) := by
  induction m with
  | zero => rw [pow_zero, Nat.cast_zero, zero_smul, nt_expS_zero]
  | succ m ih =>
    rw [pow_succ, ih, Nat.cast_succ, add_smul, one_smul,
      gt_expS_add _ _ (by rw [nt_const_smul, hg, mul_zero]) hg]
end GlobalTheory.PullbackColumn
