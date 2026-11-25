-- Prove2me | solution 1 for GlobalTheory.EffCartierData.coe_nonzeroLocus_canonical_eq_compl_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:25.268534+00:00
-- url     : https://prove2.me/submissions/42f27760-8455-44dc-9f4b-318ee65f89e3

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
theorem _root_.solution :
    (Out.nonzeroLocus D.canonical : Set X) = (Set.range D.zeroSchemeι)ᶜ := by
  rw [Scheme.IdealSheafData.range_subschemeι, coe_nonzeroLocus_canonical]
end GlobalTheory.EffCartierData
