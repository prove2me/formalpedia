-- Prove2me | solution 1 for GlobalTheory.AugCot.smooth_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:49:07.576321+00:00
-- url     : https://prove2.me/submissions/f80678ae-df73-4b48-9db5-e1e003c8a900

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_FinrankOfIsStandardSmoothOfRelativeDimension

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
    (h : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension n) (algebraMap R A)) :
    Algebra.Smooth R A := by
  rw [← RingHom.smooth_algebraMap, RingHom.smooth_iff_locally_isStandardSmooth]
  exact RingHom.locally_of_locally
    (fun hf => RingHom.IsStandardSmoothOfRelativeDimension.isStandardSmooth n _ hf) h
end GlobalTheory.AugCot
