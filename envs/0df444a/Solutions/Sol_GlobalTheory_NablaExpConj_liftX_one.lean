-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.liftX_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:49:12.954548+00:00
-- url     : https://prove2.me/submissions/db82907e-b122-4774-b3fa-539c8c64b1ea

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Theorems.Thm_GlobalTheory_NablaExpConj_liftX_hasSubst
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_one__c4430122d0d4


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
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.NablaExpConj
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k]
namespace GlobalTheory.NablaExpConj
theorem _root_.solution : liftX k (1 : PS k 1 d) = 1 :=
  FormalCalc.subst_one' (liftX_hasSubst k)
end GlobalTheory.NablaExpConj
