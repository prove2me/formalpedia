-- Prove2me | solution 1 for GlobalTheory.EffCartierData.lb_ofSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:45:34.300807+00:00
-- url     : https://prove2.me/submissions/8895fc2e-9462-41e8-8a88-543f320075d2

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
open GlobalTheory.EffCartierData
variable {X Y Z : Scheme.{0}}
variable (D D' : EffCartierData X)
namespace GlobalTheory.EffCartierData
theorem _root_.solution {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) :
    (ofSec hL s hs).lb = L := by
  have : (ofSec hL s hs).trans = L.g := funext fun i => funext fun j =>
    ((ofSec hL s hs).eq_trans i j (s.compat i j)).symm
  exact congrArg (LB.mk L.ι L.U) this
end GlobalTheory.EffCartierData
