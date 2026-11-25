-- Prove2me | solution 1 for GlobalTheory.EffCartierData.associated_of_idealSheaf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:50.4521+00:00
-- url     : https://prove2.me/submissions/a226b302-8165-4497-92dc-24427984603b

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_associated_of_germ


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
theorem _root_.solution (h : D.idealSheaf = D'.idealSheaf) (p : D'.ι) (q : D.ι) :
    Associated (resG X (inf_le_right : D'.U p ⊓ D.U q ≤ D.U q) (D.f q))
      (resG X (inf_le_left : D'.U p ⊓ D.U q ≤ D'.U p) (D'.f p)) :=
  ((D.regular q).resG _).associated_of_germ ((D'.regular p).resG _) fun x hx => by
    rw [germ_resG, germ_resG, ← stalkId_idealSheaf, ← stalkId_idealSheaf, h]
end GlobalTheory.EffCartierData
