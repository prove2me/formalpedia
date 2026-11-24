-- Prove2me | solution 1 for GlobalTheory.CommuteInvLeft.commute_inv_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:16:03.298838+00:00
-- url     : https://prove2.me/submissions/96da00ab-0b42-48ba-8561-9f97c7809f59

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CommuteInvLeft

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CommuteInvLeft
namespace GlobalTheory.CommuteInvLeft
theorem _root_.solution : ∀ {B : Type} [inst : Ring B] {x xi y : B},
    x * xi = (1 : B) → xi * x = (1 : B) → Commute x y → Commute xi y := by
  intro B _ x xi y h1 h2 h
  have h' : x * y = y * x := h
  show xi * y = y * xi
  calc xi * y = xi * y * (x * xi) := by rw [h1, mul_one]
    _ = xi * (y * x) * xi := by simp only [mul_assoc]
    _ = xi * (x * y) * xi := by rw [h']
    _ = (xi * x) * y * xi := by simp only [mul_assoc]
    _ = y * xi := by rw [h2, one_mul]
end GlobalTheory.CommuteInvLeft
