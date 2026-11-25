-- Prove2me | solution 1 for GlobalTheory.EffCartierData.existsUnique_iso_pull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:12:52.484558+00:00
-- url     : https://prove2.me/submissions/e6d80557-38e2-4fc9-829f-10738ca38c3d

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
theorem _root_.solution (φ : Y ⟶ X) (h : D.KeepsRegular φ) :
    ∃! w : LB.Iso (D.pull φ h).lb (D.lb.pull φ),
      w.IsGen ∧ SecMaps w (D.pull φ h).canonical (secPull D.canonical φ) :=
  existsUnique_secMaps (D.pull φ h).regular fun p q => by
    have := ((D.pull φ h).assoc q (p ⟨⟩)).map (resG Y
      (le_inf inf_le_right (inf_le_left.trans (pull_U D.lb φ p).le) :
        (D.lb.pull φ).U p ⊓ (D.pull φ h).U q ≤ (D.pull φ h).U q ⊓ (D.pull φ h).U (p ⟨⟩)))
    rw [resG_resG, resG_resG] at this
    exact (congrArg (Associated _) (resG_resG _ _ _)).mpr this
end GlobalTheory.EffCartierData
