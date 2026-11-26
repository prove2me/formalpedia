-- Prove2me | solution 1 for GlobalTheory.exists_star_ne
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:48:39.931047+00:00
-- url     : https://prove2.me/submissions/ec43bbbd-7357-454c-a22c-1d037875f0c2

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
variable (E)
theorem _root_.solution : ∃ x : E, star x ≠ x := by
  first
    | (have h := NumberField.IsCMField.complexConj_ne_one E
       have : ∃ x : E, NumberField.IsCMField.complexConj E x ≠ x := by
         by_contra hc
         push Not at hc
         exact h (AlgEquiv.ext fun x => by simpa using hc x)
       obtain ⟨x, hx⟩ := this
       refine ⟨x, fun hs => hx ?_⟩
       first
         | (rw [← GlobalTheory.star_eq_complexConj]; exact hs)
         | exact hs
         | (rw [← GlobalTheory.star_eq_complexConj E]; exact hs))

