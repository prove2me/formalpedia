-- Prove2me | solution 1 for GlobalTheory.T.periodic_left_halfPlane_shift_nonneg_of_im_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:05.558907+00:00
-- url     : https://prove2.me/submissions/47c96eee-bb3c-43d5-ae97-8432bf1d7c21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodicLeftHalfPlaneShiftNonnegOfImPos
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PeriodicLeftHalfPlaneShiftNonnegOfImPosStatement
import Theorems.Thm_GlobalTheory_periodic_strip_shift_nonneg


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (c : ℝ) (f : ℂ → ℂ) (m : ℤ), DifferentiableOn ℂ f {s : ℂ | s.re < c} → (∀ s : ℂ, s.re < c → f (s + 2 * Real.pi * Complex.I) = f s + m) → (∀ s : ℂ, s.re < c → 0 < (f s).im) → 0 ≤ m := by
  first | exact @GlobalTheory.periodic_strip_shift_nonneg | exact GlobalTheory.periodic_strip_shift_nonneg | (intros; apply GlobalTheory.periodic_strip_shift_nonneg <;> assumption)
end _root_.GlobalTheory.T
