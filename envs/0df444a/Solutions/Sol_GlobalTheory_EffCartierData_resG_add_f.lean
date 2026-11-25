-- Prove2me | solution 1 for GlobalTheory.EffCartierData.resG_add_f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:29:40.49297+00:00
-- url     : https://prove2.me/submissions/158db23d-0894-4463-b966-0d6c754fbf4b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange

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
theorem _root_.solution (i : D.ι) (j : D'.ι) {W : X.Opens} (h : W ≤ D.U i ⊓ D'.U j) :
    resG X h ((D.add D').f (i, j)) =
      resG X (h.trans inf_le_left) (D.f i) * resG X (h.trans inf_le_right) (D'.f j) := by
  refine (map_mul (resG X h) _ _).trans ?_
  rw [resG_resG, resG_resG]
end GlobalTheory.EffCartierData
