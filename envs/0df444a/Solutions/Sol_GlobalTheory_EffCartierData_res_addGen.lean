-- Prove2me | solution 1 for GlobalTheory.EffCartierData.res_addGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:27:04.328214+00:00
-- url     : https://prove2.me/submissions/ef890bb2-1bb1-4df8-8faf-40e91d445122

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_res_res


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
theorem _root_.solution (i j : D.ι) (i' j' : D'.ι) {W : X.Opens}
    (h : W ≤ D.U i ⊓ D'.U i' ⊓ D.U j ⊓ D'.U j') :
    res h ((D.addGen D').s (((i, i'), j), j')) =
      res (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans inf_le_left)))
        (h.trans (inf_le_left.trans inf_le_right))) (D.trans i j) *
      res (le_inf (h.trans (inf_le_left.trans (inf_le_left.trans inf_le_right)))
        (h.trans inf_le_right)) (D'.trans i' j') := by
  refine (map_mul (res h) _ _).trans ?_
  rw [LB.res_res, LB.res_res]
end GlobalTheory.EffCartierData
