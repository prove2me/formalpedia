-- Prove2me | solution 1 for GlobalTheory.NablaExpConj.pderiv_inr_liftX
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:49:06.910057+00:00
-- url     : https://prove2.me/submissions/907d3765-4da4-4eb2-9a01-111aa6e24008

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ConnectionKillsSeries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FormalExpMulFormalExpNeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_RingsOfIntegers_ExpSNegMulExpS
import Theorems.Thm_GlobalTheory_NablaExpConj_liftX_hasSubst
import Theorems.Thm_GlobalTheory_FormalCalc_pderiv_subst


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
theorem _root_.solution (f : PS k 1 d) (i : Fin d) : pderiv k (Sum.inr i) (liftX k f) = 0 := by
  unfold liftX
  rw [FormalCalc.pderiv_subst (liftX_hasSubst k)]
  refine Finset.sum_eq_zero fun p _ => ?_
  rw [pderiv_X_of_ne Sum.inl_ne_inr, mul_zero]
end GlobalTheory.NablaExpConj
