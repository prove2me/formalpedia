-- Prove2me | solution 1 for GlobalTheory.CubeFace.differentiableOn_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:02:46.131851+00:00
-- url     : https://prove2.me/submissions/f52ce27d-4f8f-400d-a864-f067531e2cbe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EntireApplyEqOfPeriodicOfSpanReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_CubeSectionFacesAndDoubling

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
open GlobalTheory
open GlobalTheory.CubeFace
namespace GlobalTheory.CubeFace
theorem _root_.solution {E α : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {U : Set E} (s : Finset α) (f : α → E → ℂ) (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) U) :
    DifferentiableOn ℂ (fun y => ∏ i ∈ s, f i y) U := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentiableOn_const (1 : ℂ)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (hf a (Finset.mem_insert_self _ _)).fun_mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))
end GlobalTheory.CubeFace
