-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.liftX_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:05.310003+00:00
-- url     : https://prove2.me/submissions/bcb6da94-5136-4473-b26f-dfc434997773

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Theorems.Thm_GlobalTheory_NablaExpConj_liftX_hasSubst
import Theorems.Thm_P2M_GlobalTheory_FormalCalc_subst_sum__4ef444666b63


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
theorem _root_.solution {ι : Type} (s : Finset ι) (f : ι → PS k 1 d) :
    liftX k (∑ i ∈ s, f i) = ∑ i ∈ s, liftX k (f i) :=
  FormalCalc.subst_sum' (liftX_hasSubst k) s f
end GlobalTheory.NablaExpConj
