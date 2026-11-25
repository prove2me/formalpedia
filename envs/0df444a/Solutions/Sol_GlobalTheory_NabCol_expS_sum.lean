-- Prove2me | solution 1 for GlobalTheory.NabCol.expS_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:06:57.951686+00:00
-- url     : https://prove2.me/submissions/57b84c47-4a24-4f9e-9195-7b18c26d71da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_JetsOnCopiesCompatibleFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_TwistBCPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_InvariantDerivationsCommuteFormalConnection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumSupportRename
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
open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PowGerm
open GlobalTheory GlobalTheory.NabCol
variable {k : Type} [CommRing k] {d n : ℕ}
namespace GlobalTheory.NabCol
theorem _root_.solution [Algebra ℚ k] {J : Type} (s : Finset J) (g : J → PS k n d) (hg : ∀ j, constantCoeff (g j) = 0) :
    FB.expS k (∑ j ∈ s, g j) = ∏ j ∈ s, FB.expS k (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.prod_empty]
    unfold FB.expS
    have hs : PowerSeries.HasSubst (0 : PS k n d) := PowerSeries.HasSubst.of_constantCoeff_zero (by simp)
    ext m
    rw [PowerSeries.coeff_subst hs, finsum_eq_single _ 0]
    · simp
    · intro r hr
      simp [hr]
  | insert c s hc ih =>
    rw [Finset.sum_insert hc, Finset.prod_insert hc, gt_expS_add _ _ (hg c) (by simp [hg]), ih]
end GlobalTheory.NabCol
