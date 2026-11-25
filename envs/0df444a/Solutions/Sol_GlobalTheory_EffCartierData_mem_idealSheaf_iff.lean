-- Prove2me | solution 1 for GlobalTheory.EffCartierData.mem_idealSheaf_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:39:49.479321+00:00
-- url     : https://prove2.me/submissions/9474ce04-1511-46cf-8c45-78ec310535b8

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_dvd_of_germ


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
theorem _root_.solution {W : X.affineOpens} {a : Γ(X, W.1)} :
    a ∈ D.idealSheaf.ideal W ↔ ∀ i, resG X (inf_le_right : W.1 ⊓ D.U i ≤ D.U i) (D.f i) ∣
      resG X (inf_le_left : W.1 ⊓ D.U i ≤ W.1) a := by
  refine (mem_locIdeal_iff _ _ _ _).trans ⟨fun h i => ?_, fun h i x hx hi => ?_⟩
  · refine ((D.regular i).resG _).dvd_of_germ fun x hx => ?_
    rw [germ_resG, germ_resG]
    exact h i x hx.1 hx.2
  · have hm : x ∈ W.1 ⊓ D.U i := ⟨hx, hi⟩
    have := map_dvd (X.presheaf.germ _ x hm).hom (h i)
    rwa [germ_resG, germ_resG] at this
end GlobalTheory.EffCartierData
