-- Prove2me | solution 1 for GlobalTheory.HodgeTateTest.omega_le_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:37:37.575521+00:00
-- url     : https://prove2.me/submissions/0a8b1ea7-590c-4ab4-ac06-e52b40d636a5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsUniqueIsAl
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_HtCharOfIsUnit
import Theorems.Thm_GlobalTheory_HodgeTateTest_lie_iff
import Theorems.Thm_GlobalTheory_HodgeTateTest_fst_eq
import Theorems.Thm_GlobalTheory_HodgeTateTest_dlogT_mem
import Theorems.Thm_GlobalTheory_HodgeTateTest_dlogT_bijective
import Theorems.Thm_GlobalTheory_GmPoints_unitOf_ptMap
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv
open GlobalTheory GlobalTheory.HodgeTateTest
open GlobalTheory.TangentPow GlobalTheory.GmPoints GlobalTheory.HodgeTateImage
variable {O : Type} [CommRing O]
namespace GlobalTheory.HodgeTateTest
theorem _root_.solution : omega (GmO O) ≤ Submodule.span O {dlogT} := by
  intro f hf
  obtain ⟨e, he⟩ := (dlogT_bijective (O := O)).2 1
  rw [Submodule.mem_span_singleton]
  refine ⟨f e, funext fun x => ?_⟩
  have h1 : (unitOf (ptMap (dualScale (dlogT x)) ≫ e.1) : DualNumber O).fst = 1 := by
    rw [unitOf_ptMap]; simp [dualScale, fst_eq]
  have hm := (lie_iff _).2 h1
  have hx : x = ⟨ptMap (dualScale (dlogT x)) ≫ e.1, hm⟩ := by
    apply (dlogT_bijective (O := O)).1
    rw [dlogT_mem.2 _ e hm, he, _root_.mul_one]
  have := hf.2 (dlogT x) e hm
  rw [← hx] at this
  simp [this, mul_comm]
end GlobalTheory.HodgeTateTest
