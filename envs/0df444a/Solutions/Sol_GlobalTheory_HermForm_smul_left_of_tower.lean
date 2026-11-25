-- Prove2me | solution 1 for GlobalTheory.HermForm.smul_left_of_tower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:58:57.905697+00:00
-- url     : https://prove2.me/submissions/2216bf49-8acc-4a9e-a495-1b7a373951be

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
namespace GlobalTheory
namespace HermForm
theorem _root_.solution {S R M : Type*} [CommRing S] [CommRing R] [StarRing R]
    [Algebra S R] [AddCommGroup M] [Module R M] [Module S M]
    [IsScalarTower S R M] (h : HermForm R M) (a : S) (x y : M) :
    h (a • x) y = algebraMap S R a * h x y := by
  rw [← algebraMap_smul R a x, h.smul_left]
end HermForm
end GlobalTheory
