-- Prove2me | solution 1 for GlobalTheory.EffCartierData.coe_nonzeroLocus_eq_compl_support_ofSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:31.311769+00:00
-- url     : https://prove2.me/submissions/6dbae79a-e230-444e-9884-6ad31c333d70

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
theorem _root_.solution {L : LB X} (hL : L.IsLB) (s : L.Sec)
    (hs : IsRegularSec s) :
    (Out.nonzeroLocus s : Set X) = ((ofSec hL s hs).idealSheaf.support : Set X)ᶜ :=
  (ofSec hL s hs).coe_nonzeroLocus_canonical
end GlobalTheory.EffCartierData
