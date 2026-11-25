-- Prove2me | solution 1 for GlobalTheory.HermForm.smul_right_of_isStarFixed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:59:02.404637+00:00
-- url     : https://prove2.me/submissions/4aca37d3-4c71-4960-ae2e-59902b7535e5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
import Theorems.Thm_GlobalTheory_HermForm_smul_right

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
namespace GlobalTheory
namespace HermForm
theorem _root_.solution {F R M : Type*} [CommRing F] [CommRing R] [StarRing R]
    [Algebra F R] [IsStarFixed F R] [AddCommGroup M] [Module R M] [Module F M]
    [IsScalarTower F R M] (h : HermForm R M) (a : F) (x y : M) : h x (a • y) = a • h x y := by
  rw [← algebraMap_smul R a y, h.smul_right, IsStarFixed.star_algebraMap, Algebra.smul_def]
end HermForm
end GlobalTheory
