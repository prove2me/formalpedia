-- Prove2me | solution 1 for GlobalTheory.EffCartierData.bijOn_poleSecs_global
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:13.119337+00:00
-- url     : https://prove2.me/submissions/e817b60d-ad39-4423-be2b-acda85451d4d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_bijOn_secOnOf_top
import Theorems.Thm_GlobalTheory_EffCartierData_bijOn_poleSecs_lbPow
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
theorem _root_.solution (n : ℕ) :
    Set.BijOn (fun t => ratOf (D.isLB_lbPow n) (secPow D.canonical n) ⊤ (secOnOf t ⊤)) Set.univ
      (D.poleSecs n ⊤) :=
  (D.bijOn_poleSecs_lbPow n ⊤).comp (bijOn_secOnOf_top _)
end GlobalTheory.EffCartierData
