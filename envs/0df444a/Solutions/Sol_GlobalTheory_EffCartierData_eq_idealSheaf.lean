-- Prove2me | solution 1 for GlobalTheory.EffCartierData.eq_idealSheaf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:11:53.48903+00:00
-- url     : https://prove2.me/submissions/ef7e0fa8-2c33-4a95-858a-c5bd9e8e2128

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
theorem _root_.solution {I : X.IdealSheafData}
    (h : ∀ x : X, ∃ (W : X.affineOpens) (i : D.ι) (hW : W.1 ≤ D.U i),
      x ∈ W.1 ∧ I.ideal W = Ideal.span {resG X hW (D.f i)}) : I = D.idealSheaf := by
  choose W i hW hx hI using h
  exact Scheme.IdealSheafData.ext_of_iSup_eq_top W
    (eq_top_iff.2 fun x _ => Opens.mem_iSup.2 ⟨x, hx x⟩)
    fun x => (hI x).trans (D.ideal_idealSheaf _ _ _).symm
end GlobalTheory.EffCartierData
