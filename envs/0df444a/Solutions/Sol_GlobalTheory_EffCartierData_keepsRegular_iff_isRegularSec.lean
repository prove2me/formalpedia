-- Prove2me | solution 1 for GlobalTheory.EffCartierData.keepsRegular_iff_isRegularSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:58.017083+00:00
-- url     : https://prove2.me/submissions/847953ae-ad6a-4c4e-bd24-aaa6c9035ee4

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_resG_self


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
theorem _root_.solution (φ : Y ⟶ X) :
    D.KeepsRegular φ ↔ IsRegularSec (secPull D.canonical φ) := by
  refine ⟨fun h j => (h (j ⟨⟩)).resG _, fun h i => ?_⟩
  have := (h fun _ => i).resG (pull_U D.lb φ fun _ => i).ge
  exact (congrArg IsRegularFn ((resG_resG _ _ _).trans (resG_self _ _))).mp this
end GlobalTheory.EffCartierData
