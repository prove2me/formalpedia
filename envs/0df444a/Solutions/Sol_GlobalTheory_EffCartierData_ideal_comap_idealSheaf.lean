-- Prove2me | solution 1 for GlobalTheory.EffCartierData.ideal_comap_idealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:33:57.777871+00:00
-- url     : https://prove2.me/submissions/45930e17-d9c5-47a7-a6d5-02ca0160662a

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
theorem _root_.solution (φ : Y ⟶ X) (W : Y.affineOpens) (i : D.ι)
    (h : W.1 ≤ φ ⁻¹ᵁ D.U i) :
    (D.idealSheaf.comap φ).ideal W = Ideal.span {resG Y h ((φ.app (D.U i)).hom (D.f i))} := by
  rw [comap_idealSheaf]
  exact ideal_locIdeal _ _ _ _ W i h
end GlobalTheory.EffCartierData
