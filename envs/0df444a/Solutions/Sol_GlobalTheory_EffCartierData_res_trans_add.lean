-- Prove2me | solution 1 for GlobalTheory.EffCartierData.res_trans_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:42:42.550247+00:00
-- url     : https://prove2.me/submissions/0dd8eb25-58f1-40bd-baad-a35dbf9b9fb9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_resG_add_f

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
open GlobalTheory
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open Cartier
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution (p q : D.ι × D'.ι) {W : X.Opens} (hp : W ≤ D.U p.1 ⊓ D'.U p.2)
    (hq : W ≤ D.U q.1 ⊓ D'.U q.2) :
    res (le_inf hp hq) ((D.add D').trans p q) =
      res (le_inf (hp.trans inf_le_left) (hq.trans inf_le_left)) (D.trans p.1 q.1) *
        res (le_inf (hp.trans inf_le_right) (hq.trans inf_le_right)) (D'.trans p.2 q.2) := by
  refine Units.ext ((D.add D').eq_trans_on p q hp hq ?_).symm
  refine (D.resG_add_f D' p.1 p.2 hp).trans (Eq.trans ?_
    (congrArg _ (D.resG_add_f D' q.1 q.2 hq)).symm)
  rw [D.trans_spec_on p.1 q.1 _ (hq.trans inf_le_left),
    D'.trans_spec_on p.2 q.2 _ (hq.trans inf_le_right), mul_mul_mul_comm]
  rfl
end GlobalTheory.EffCartierData
