-- Prove2me | solution 1 for GlobalTheory.EffCartierData.lbIso_of_idealSheaf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:25.518468+00:00
-- url     : https://prove2.me/submissions/5819d9d4-e6f1-44d7-a7a7-bb3da29c07f1

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_existsUnique_iso_of_idealSheaf_eq

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
theorem _root_.solution (h : D.idealSheaf = D'.idealSheaf) : LBIso D.lb D'.lb :=
  (D.existsUnique_iso_of_idealSheaf_eq D' h).exists.imp fun _ hw => hw.1
end GlobalTheory.EffCartierData
