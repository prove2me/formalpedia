-- Prove2me | solution 1 for GlobalTheory.StarTensor.add_star_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:12:20.146044+00:00
-- url     : https://prove2.me/submissions/5a459f88-fa21-400f-86d8-2bce13b46b6c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_StarTensor_add_tmul
import Theorems.Thm_GlobalTheory_StarTensor_smul_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
universe u v
attribute [instance] HermModule.addCommGroup HermModule.module
attribute [instance] HermSpace.addCommGroup HermSpace.module HermSpace.finite
attribute [simp] IsStarFixed.star_algebraMap
open GlobalTheory.StarTensor
variable {F E A : Type*} [CommRing F] [CommRing E] [CommRing A] [Algebra F E] [Algebra F A]
  [StarRing E] [IsStarFixed F E]
variable {B : Type*} [CommRing B] [Algebra F B]
namespace GlobalTheory.StarTensor
theorem _root_.solution (hE : ∀ e : E, e + star e ∈ (algebraMap F E).range)
    (x : StarTensor F E A) : x + star x ∈ (algebraMap A (StarTensor F E A)).range := by
  refine x.induction_on (by simp) (fun e a => ?_) (fun x y hx hy => ?_)
  · obtain ⟨c, hc⟩ := hE e
    refine ⟨c • a, ?_⟩
    rw [star_tmul, ← add_tmul, ← hc, algebraMap_right, ← smul_tmul, Algebra.algebraMap_eq_smul_one]
  · rw [star_add, add_add_add_comm]
    exact add_mem hx hy
end GlobalTheory.StarTensor
