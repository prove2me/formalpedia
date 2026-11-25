-- Prove2me | solution 1 for GlobalTheory.CMTensor.star_eq_self_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:29:17.788016+00:00
-- url     : https://prove2.me/submissions/1748a2b0-65c2-4e27-8efb-5ab16081cca7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_StarTensor_add_star_mem_range
import Theorems.Thm_GlobalTheory_add_star_mem

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
variable (E : Type*) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.CMTensor
variable {A : Type*} [CommRing A] [Algebra (maximalRealSubfield E) A]
namespace GlobalTheory.CMTensor
theorem _root_.solution (x : CMTensor E A) :
    star x = x ↔ x ∈ (algebraMap A (CMTensor E A)).range := by
  refine ⟨fun hx => ?_, ?_⟩
  · obtain ⟨a, ha⟩ := StarTensor.add_star_mem_range
      (fun e : E => ⟨⟨_, add_star_mem e⟩, rfl⟩) x
    refine ⟨(2 : maximalRealSubfield E)⁻¹ • a, ?_⟩
    rw [Algebra.smul_def, map_mul, ha, hx, ← IsScalarTower.algebraMap_apply, ← two_mul,
      ← mul_assoc, ← map_ofNat (algebraMap (maximalRealSubfield E) (CMTensor E A)) 2, ← map_mul,
      inv_mul_cancel₀ two_ne_zero, map_one, one_mul]
  · rintro ⟨a, rfl⟩
    exact IsStarFixed.star_algebraMap a
end GlobalTheory.CMTensor
