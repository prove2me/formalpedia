-- Prove2me | solution 1 for GlobalTheory.EffCartierData.bijOn_poleSecs_lbPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:42:33.672502+00:00
-- url     : https://prove2.me/submissions/27e9f39a-5677-4b6c-b27d-7210eeba24f0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_existsUnique_iso_nsmul
import Theorems.Thm_GlobalTheory_Cartier_IsRegularSec_secPow
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
theorem _root_.solution (n : ℕ) (V : X.Opens) [Nonempty V] :
    Set.BijOn (ratOf (D.isLB_lbPow n) (secPow D.canonical n) V) (secOn (lbPow D.lb n) V)
      (D.poleSecs n V) := by
  obtain ⟨w, ⟨-, hw⟩, -⟩ := D.existsUnique_iso_nsmul n
  rw [poleSecs, hw.ratSecs_eq (D.nsmul n).isLB_lb (D.isLB_lbPow n) V]
  exact bijOn_ratOf _ (D.isRegularSec_canonical.secPow n) V
end GlobalTheory.EffCartierData
