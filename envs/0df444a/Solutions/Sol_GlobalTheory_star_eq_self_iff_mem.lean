-- Prove2me | solution 1 for GlobalTheory.star_eq_self_iff_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:25.14613+00:00
-- url     : https://prove2.me/submissions/9cde8cb4-657d-46c3-88ff-d2f2b04590a0

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
namespace GlobalTheory
theorem _root_.solution (x : E) : star x = x ↔ x ∈ maximalRealSubfield E :=
  IsCMField.complexConj_eq_self_iff E x
end GlobalTheory
