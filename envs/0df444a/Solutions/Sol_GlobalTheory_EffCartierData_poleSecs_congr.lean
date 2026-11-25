-- Prove2me | solution 1 for GlobalTheory.EffCartierData.poleSecs_congr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:42:19.898817+00:00
-- url     : https://prove2.me/submissions/11b0f481-7a43-4b28-9b10-a3bcd4c0b708

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_idealSheaf_eq_iff
import Theorems.Thm_GlobalTheory_EffCartierData_idealSheaf_nsmul
import Theorems.Thm_GlobalTheory_Cartier_SecMaps_ratSecs_eq


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
theorem _root_.solution (h : D.idealSheaf = D'.idealSheaf) (n : ℕ) (V : X.Opens) [Nonempty V] :
    D.poleSecs n V = D'.poleSecs n V := by
  obtain ⟨w, -, hw⟩ := ((D.nsmul n).idealSheaf_eq_iff (D'.nsmul n)).1
    (by rw [idealSheaf_nsmul, idealSheaf_nsmul, h])
  exact hw.ratSecs_eq (D.nsmul n).isLB_lb (D'.nsmul n).isLB_lb V
end GlobalTheory.EffCartierData
