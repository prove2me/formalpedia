-- Prove2me | solution 1 for GlobalTheory.EffCartierData.existsUnique_iso_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:28:42.163932+00:00
-- url     : https://prove2.me/submissions/210c92a6-0938-4b84-873d-2606ba39b240

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_IsRegularSec_secPow
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
theorem _root_.solution (n : ℕ) :
    ∃! w : LB.Iso (D.nsmul n).lb (lbPow D.lb n),
      w.IsGen ∧ SecMaps w (D.nsmul n).canonical (secPow D.canonical n) :=
  existsUnique_secMaps (D.nsmul n).regular fun p q => by
    have := ((D.nsmul n).assoc q (p ⟨⟩)).map (resG X
      (le_inf inf_le_right (inf_le_left.trans (lbPow_U D.lb n p).le) :
        (lbPow D.lb n).U p ⊓ (D.nsmul n).U q ≤ (D.nsmul n).U q ⊓ (D.nsmul n).U (p ⟨⟩)))
    rw [resG_resG, resG_resG] at this
    refine (congrArg (Associated _) ?_).mpr this
    exact (congrArg _ (map_pow (resG X (lbPow_U D.lb n p).le) _ n).symm).trans (resG_resG _ _ _)
end GlobalTheory.EffCartierData
