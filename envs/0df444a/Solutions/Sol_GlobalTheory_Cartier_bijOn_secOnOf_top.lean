-- Prove2me | solution 1 for GlobalTheory.Cartier.bijOn_secOnOf_top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:29:29.700452+00:00
-- url     : https://prove2.me/submissions/3ae79464-b90d-4967-819b-82e0475e5470

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_DivSheaf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_CoeNonzeroLocusCanonicalEqComplRange
import Theorems.Thm_GlobalTheory_Cartier_secOnOf_mem
import Theorems.Thm_GlobalTheory_Cartier_resG_self
import Theorems.Thm_GlobalTheory_Cartier_sec_ext


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
open GlobalTheory.Cartier
variable {X : Scheme.{0}}
namespace GlobalTheory.Cartier
theorem _root_.solution (L : LB X) :
    Set.BijOn (fun t : L.Sec => secOnOf t ⊤) Set.univ (secOn L ⊤) := by
  have le : ∀ i, L.U i ≤ ⊤ ⊓ L.U i := fun i => le_inf le_top le_rfl
  refine ⟨fun t _ => secOnOf_mem t ⊤, fun t _ t' _ e => sec_ext fun i => ?_, fun t ht => ?_⟩
  · have := congrArg (resG X (le i)) (congrFun e i)
    simp only [secOnOf, resG_resG, resG_self] at this
    exact this
  · refine ⟨⟨fun i => resG X (le i) (t i), fun i j => ?_⟩, trivial, funext fun i =>
      (resG_resG _ _ _).trans (resG_self _ _)⟩
    have := congrArg (resG X (inf_le_inf_right _ (le i) : L.U i ⊓ L.U j ≤ ⊤ ⊓ L.U i ⊓ L.U j))
      (ht i j)
    rw [map_mul, resG_resG, resG_resG, resG_resG, resG_self] at this
    exact (resG_resG _ _ _).trans (this.trans (congrArg _ (resG_resG _ _ _).symm))
end GlobalTheory.Cartier
