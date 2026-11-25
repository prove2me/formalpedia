-- Prove2me | solution 1 for GlobalTheory.EffCartierData.existsUnique_iso_ofSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:51:15.85763+00:00
-- url     : https://prove2.me/submissions/9ef69f9e-4d52-495d-bde1-5f90d1bbc2d3

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
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
theorem _root_.solution {L : LB X} (hL : L.IsLB) (s : L.Sec) (hs : IsRegularSec s) :
    ∃! w : LB.Iso L (ofSec hL s hs).lb, w.IsGen ∧ SecMaps w s (ofSec hL s hs).canonical :=
  existsUnique_secMaps hs fun p q => ((ofSec hL s hs).assoc p q).symm
end GlobalTheory.EffCartierData
