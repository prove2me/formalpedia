-- Prove2me | solution 1 for GlobalTheory.Cartier.secOnOf_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:12:25.356192+00:00
-- url     : https://prove2.me/submissions/5e61a04c-247a-419c-ba09-32b185aaffed

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
open GlobalTheory.Cartier
variable {X : Scheme.{0}}
namespace GlobalTheory.Cartier
theorem _root_.solution {L : LB X} (t : L.Sec) (V : X.Opens) : secOnOf t V ∈ secOn L V := fun i j =>
  (resG_resG _ _ _).trans ((sec_compat t i j (inf_le_left.trans inf_le_right) inf_le_right).trans
    (congrArg _ (resG_resG _ _ _).symm))
end GlobalTheory.Cartier
