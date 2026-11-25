-- Prove2me | solution 1 for GlobalTheory.EffCartierData.effCartier_idealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:42:36.679231+00:00
-- url     : https://prove2.me/submissions/4bd29920-11d9-4f8d-ba7f-d713c4ea04b0

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
theorem _root_.solution : FinalTheorems.EffCartier D.idealSheaf := fun x => by
  obtain ⟨i, hi⟩ := D.exists_mem x
  obtain ⟨W, hxW, hW⟩ := exists_affine_le hi
  exact ⟨W, _, hxW, D.regular i _ hW, D.ideal_idealSheaf W i hW⟩
end GlobalTheory.EffCartierData
