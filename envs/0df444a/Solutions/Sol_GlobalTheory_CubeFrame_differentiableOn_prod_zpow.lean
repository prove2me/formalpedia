-- Prove2me | solution 1 for GlobalTheory.CubeFrame.differentiableOn_prod_zpow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:01:54.913796+00:00
-- url     : https://prove2.me/submissions/621683bc-1bcc-4c0f-ba2f-1410a9455a48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsGlobalFrameOfLocal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix Filter Topology
open scoped BigOperators Real
open GlobalTheory GlobalTheory.CubeFrame
namespace GlobalTheory.CubeFrame
theorem _root_.solution {X α : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    {U : Set X} (s : Finset α) {f : α → X → ℂ} (e : α → ℤ)
    (hf : ∀ a ∈ s, DifferentiableOn ℂ (f a) U) (h0 : ∀ a ∈ s, ∀ x ∈ U, f a x ≠ 0) :
    DifferentiableOn ℂ (fun x => ∏ a ∈ s, f a x ^ e a) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact ((hf a (Finset.mem_insert_self _ _)).zpow
      (Or.inl (h0 a (Finset.mem_insert_self _ _)))).mul
      (ih (fun b hb => hf b (Finset.mem_insert_of_mem hb))
        fun b hb => h0 b (Finset.mem_insert_of_mem hb))
end GlobalTheory.CubeFrame
