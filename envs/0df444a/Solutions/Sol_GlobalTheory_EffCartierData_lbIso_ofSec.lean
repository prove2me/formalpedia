-- Prove2me | solution 1 for GlobalTheory.EffCartierData.lbIso_ofSec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:54:37.771274+00:00
-- url     : https://prove2.me/submissions/08383ca0-03a1-4d79-9339-cf4883692559

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_P2M_GlobalTheory_EffCartierData_existsUnique_iso_ofSec__00c3eee85ad9

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
    LBIso (ofSec hL s hs).lb L :=
  (existsUnique_iso_ofSec' hL s hs).exists.imp fun _ hw => hw.1
end GlobalTheory.EffCartierData
