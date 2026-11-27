-- Prove2me | solution 2 for GlobalTheory.starAlgEquiv_eq_complexConj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:33.146505+00:00
-- url     : https://prove2.me/submissions/8f0b6f97-97aa-4f7f-8dbc-53f898ade53e

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
namespace GlobalTheory
theorem _root_.solution :
    starAlgEquiv (maximalRealSubfield E) E = IsCMField.complexConj E := AlgEquiv.ext fun _ => rfl
end GlobalTheory
