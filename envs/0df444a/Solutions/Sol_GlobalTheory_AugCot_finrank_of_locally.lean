-- Prove2me | solution 1 for GlobalTheory.AugCot.finrank_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:03:38.628729+00:00
-- url     : https://prove2.me/submissions/08177087-6ad4-4bac-86f4-663c31be33e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_smooth_of_locally
import Theorems.Thm_GlobalTheory_AugCot_rankAtStalk_of_locally

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory
open GlobalTheory.AugCot
universe u
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] (ε : A →ₐ[R] R) {n : ℕ}
namespace GlobalTheory.AugCot
theorem _root_.solution [IsLocalRing R]
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Module.finrank R (AugCot ε) = n := by
  haveI := smooth_of_locally h
  have := rankAtStalk_of_locally ε h (IsLocalRing.closedPoint R)
  rwa [Module.rankAtStalk_eq_finrank_of_free] at this
end GlobalTheory.AugCot
