-- Prove2me | solution 1 for GlobalTheory.EffCartierData.ratOf_secPow_canonical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:49:14.487286+00:00
-- url     : https://prove2.me/submissions/4d411c9f-dd00-415f-8b4d-b164fb7d101b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_ratOf_secOnOf_self
import Theorems.Thm_GlobalTheory_Cartier_IsRegularSec_secPow


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
variable [IsIntegral X]
namespace GlobalTheory.EffCartierData
theorem _root_.solution (n : ℕ) (V : X.Opens) [Nonempty V] :
    ratOf (D.isLB_lbPow n) (secPow D.canonical n) V (secOnOf (secPow D.canonical n) V) = 1 :=
  ratOf_secOnOf_self _ (D.isRegularSec_canonical.secPow n) V
end GlobalTheory.EffCartierData
