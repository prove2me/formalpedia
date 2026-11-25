-- Prove2me | solution 1 for GlobalTheory.HermForm.apply_self_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:53:18.127493+00:00
-- url     : https://prove2.me/submissions/93c06f88-53c4-4e92-ac47-8d5e017de3d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_star_eq_self_iff_mem

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
namespace HermForm
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module E V] (h : HermForm E V)
    (x : V) : h x x ∈ maximalRealSubfield E :=
  (star_eq_self_iff_mem _).1 (h.star_apply x x)
end HermForm
end GlobalTheory
