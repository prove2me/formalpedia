-- Prove2me | solution 1 for GlobalTheory.EffCartierData.bijOn_poleSecs_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:19.406264+00:00
-- url     : https://prove2.me/submissions/20371d49-d8c9-4e24-92f1-be5241033d40

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_idealSheaf_eq_iff
import Theorems.Thm_GlobalTheory_EffCartierData_idealSheaf_nsmul
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_ratSecs_eq
import Theorems.Thm_GlobalTheory_Cartier_bijOn_ratOf


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
theorem _root_.solution (V : X.Opens) [Nonempty V] :
    Set.BijOn (ratOf D.isLB_lb D.canonical V) (secOn D.lb V) (D.poleSecs 1 V) := by
  obtain ⟨w, -, hw⟩ := ((D.nsmul 1).idealSheaf_eq_iff D).1 (by rw [idealSheaf_nsmul, pow_one])
  rw [poleSecs, hw.ratSecs_eq (D.nsmul 1).isLB_lb D.isLB_lb V]
  exact bijOn_ratOf _ D.isRegularSec_canonical V
end GlobalTheory.EffCartierData
