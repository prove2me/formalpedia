-- Prove2me | solution 1 for GroundTheory.GroupCoh.augSES_shortExact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:28:49.806635+00:00
-- url     : https://prove2.me/submissions/109f1aed-ff3f-408f-b46c-1c837f8d4fb4

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_InducedNorm
import Definitions.Def_GroundTheory_TateCohomology_DimensionShift
import Definitions.Def_GroundTheory_TateCohomology_TateConnecting
import Definitions.Def_GroundTheory_TateCohomology_AugmentationSES
import Theorems.Thm_GroundTheory_GroupCoh_shortExact_of_linear
import Theorems.Thm_GroundTheory_GroupCoh_augSES_decomp
import Theorems.Thm_GroundTheory_GroupCoh_augSES_f_retract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open CategoryTheory MonoidalCategory
open GroundTheory GroundTheory.GroupCoh
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (k G)
variable {k G}
variable (k G)
variable {k G}
namespace GroundTheory.GroupCoh
theorem _root_.solution (X : Rep.{u} k G) : ((augSES k G).obj X).ShortExact :=
  shortExact_of_linear (Function.LeftInverse.injective (augSES_f_retract X))
    (fun (a : X) => ⟨(MonoidAlgebra.single 1 1 ⊗ₜ[k] a : (Rep.leftRegular k G ⊗ X : Rep k G)), by
      change (augX X).hom _ = a
      rw [augX_tmul, augmentation_single, one_smul]⟩)
    (fun t ht => ⟨LinearMap.rTensor X.V (augIdealRetract k G) t, by
      have h := augSES_decomp X t
      have ht' : (augX X).hom t = 0 := ht
      rw [ht', TensorProduct.tmul_zero, add_zero] at h
      exact h⟩)
end GroundTheory.GroupCoh
