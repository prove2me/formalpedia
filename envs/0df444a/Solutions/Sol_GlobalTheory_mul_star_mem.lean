-- Prove2me | solution 1 for GlobalTheory.mul_star_mem
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:32:03.097034+00:00
-- url     : https://prove2.me/submissions/7280ace4-2ca9-4ce6-b99f-a686ba476b52

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
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
theorem _root_.solution (x : E) : x * star x ∈ maximalRealSubfield E := by
  have h : ∀ y : E, NumberField.IsCMField.complexConj E y = star y :=
    fun y => by first | exact (GlobalTheory.star_eq_complexConj y).symm | exact (GlobalTheory.star_eq_complexConj E y).symm | rfl
  refine (NumberField.IsCMField.complexConj_eq_self_iff E _).1 ?_
  rw [map_mul, h, h, star_star, mul_comm]

