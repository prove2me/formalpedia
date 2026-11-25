-- Prove2me | solution 1 for GlobalTheory.PlaceModel.isBichar_neg_one_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:05:34.672285+00:00
-- url     : https://prove2.me/submissions/e9e1dc06-553c-4fbb-8c55-958fa40521dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.PlaceModel
variable {G : Type} [AddCommGroup G]
namespace GlobalTheory.PlaceModel
theorem _root_.solution : IsBichar (fun a b : ℤ => (-1 : ℂ) ^ (a * b)) := by
  have h0 : (-1 : ℂ) ≠ 0 := by norm_num
  refine ⟨fun a b y => ?_, fun a y z => ?_, fun y => ?_, fun a => ?_⟩
  · rw [add_mul, zpow_add₀ h0]
  · rw [mul_add, zpow_add₀ h0]
  · simp
  · simp
end GlobalTheory.PlaceModel
