-- Prove2me | solution 1 for GlobalTheory.HasConstSecondDiff.polarBilin_quadraticMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:54:48.38114+00:00
-- url     : https://prove2.me/submissions/5adb6e6e-5f82-4198-8311-5dfc9ad9b41a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
import Theorems.Thm_GlobalTheory_HasConstSecondDiff_polar_quadraticMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]
open GlobalTheory.HasConstSecondDiff
variable {f : X → A}
namespace GlobalTheory.HasConstSecondDiff
theorem _root_.solution (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) :
    (h.quadraticMap he).polarBilin = h.bilin :=
  LinearMap.ext₂ (h.polar_quadraticMap he)
end GlobalTheory.HasConstSecondDiff
