-- Prove2me | solution 1 for GlobalTheory.Regauge.eq_mul_expS
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:46:40.135913+00:00
-- url     : https://prove2.me/submissions/a983c076-86f0-4ccf-b3de-81ffb2f07d30

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_WickOperatorVanishing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GEWick
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeTrans
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvRegaugedSecondLawFamily

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
open GlobalTheory GlobalTheory.Regauge
variable {k : Type} [CommRing k] [Algebra ℚ k] {d : ℕ}
namespace GlobalTheory.Regauge
theorem _root_.solution {n : ℕ} (P f g : PS k n d) (hg : constantCoeff g = 0) (h : f + g = 0) :
    P = P * expR f * FB.expS k g := by
  rw [← expR_eq hg, mul_assoc, ← expR_add, h, expR_zero, mul_one]
end GlobalTheory.Regauge
