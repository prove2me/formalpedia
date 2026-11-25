-- Prove2me | solution 1 for GlobalTheory.EffCartierData.addGen_canonical
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:54:46.491662+00:00
-- url     : https://prove2.me/submissions/a3e87141-68b1-4a30-8e8f-735eda37ae77

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_EffCartierData_resG_add_f
import Theorems.Thm_GlobalTheory_EffCartierData_res_addGen

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
theorem _root_.solution (i j : D.ι) (i' j' : D'.ι) {W : X.Opens}
    (h : W ≤ D.U i ⊓ D'.U i' ⊓ D.U j ⊓ D'.U j') :
    resG X (h.trans (inf_le_left.trans inf_le_left)) ((D.add D').canonical.f (i, i')) =
      (res h ((D.addGen D').s (((i, i'), j), j')) : Γ(X, W)ˣ) *
        (resG X (h.trans (inf_le_left.trans inf_le_right)) (D.canonical.f j) *
          resG X (h.trans inf_le_right) (D'.canonical.f j')) := by
  refine (D.resG_add_f D' i i' _).trans ?_
  rw [res_addGen, D.trans_spec_on i j _ (h.trans (inf_le_left.trans inf_le_right)),
    D'.trans_spec_on i' j' _ (h.trans inf_le_right), mul_mul_mul_comm]
  rfl
end GlobalTheory.EffCartierData
