-- Prove2me | solution 1 for GlobalTheory.EffCartierData.existsUnique_iso_of_idealSheaf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:48:29.278352+00:00
-- url     : https://prove2.me/submissions/98677757-0926-492b-933e-2e9e1bbd7f7c

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_associated_of_idealSheaf_eq
import Theorems.Thm_GlobalTheory_Cartier_existsUnique_secMaps


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
theorem _root_.solution (h : D.idealSheaf = D'.idealSheaf) :
    ∃! w : LB.Iso D.lb D'.lb, w.IsGen ∧ SecMaps w D.canonical D'.canonical :=
  existsUnique_secMaps D.regular (D.associated_of_idealSheaf_eq D' h)
end GlobalTheory.EffCartierData
