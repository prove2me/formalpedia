-- Prove2me | solution 1 for GlobalTheory.EffCartierData.idealSheaf_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T15:25:35.67666+00:00
-- url     : https://prove2.me/submissions/79f2e3f6-e811-47d2-a7c2-a1c12cd45987

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_existsUnique_iso_of_idealSheaf_eq
import Theorems.Thm_GlobalTheory_EffCartierData_idealSheaf_eq_of_secMaps

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
theorem _root_.solution : D.idealSheaf = D'.idealSheaf ↔
    ∃ w : LB.Iso D.lb D'.lb, w.IsGen ∧ SecMaps w D.canonical D'.canonical :=
  ⟨fun h => (D.existsUnique_iso_of_idealSheaf_eq D' h).exists,
    fun ⟨_, hw⟩ => D.idealSheaf_eq_of_secMaps D' hw.2⟩
end GlobalTheory.EffCartierData
