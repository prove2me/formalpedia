-- Prove2me | solution 1 for GlobalTheory.AugCot.rankAtStalk_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T12:47:15.558976+00:00
-- url     : https://prove2.me/submissions/a8f347f4-3a85-44e8-ad8f-acee168d60cb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension
import Theorems.Thm_GlobalTheory_AugCot_rankAtStalk_eq
import Theorems.Thm_GlobalTheory_AugCot_smooth_of_locally
import Theorems.Thm_GlobalTheory_AugCot_rankAtStalk_kaehler_of_locally

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
theorem _root_.solution
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A))
    (p : PrimeSpectrum R) : Module.rankAtStalk (AugCot ε) p = n := by
  haveI := smooth_of_locally h
  rw [rankAtStalk_eq, rankAtStalk_kaehler_of_locally h]
end GlobalTheory.AugCot
