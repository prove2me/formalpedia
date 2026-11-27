-- Prove2me | solution 1 for GlobalTheory.UTrans.isHerm_hyperbolic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:35:23.57861+00:00
-- url     : https://prove2.me/submissions/094f8f25-6305-4db8-b509-b454ae5e8bae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}
namespace GlobalTheory.UTrans
theorem _root_.solution : IsHerm (starRingEnd ℂ) !![0, 1; 1, 0] ∧
    ∃ z : Fin 2 → ℂ, z ≠ 0 ∧ hf (starRingEnd ℂ) !![0, 1; 1, 0] z z = 0 := by
  refine ⟨⟨by simp, ⟨Complex.I, ?_⟩, ?_, by simp [Matrix.det_fin_two]⟩, ![1, 0], ?_, by simp [hf, Fin.sum_univ_two]⟩
  · intro h
    have := congrArg Complex.im h
    norm_num at this
  · intro a b; fin_cases a <;> fin_cases b <;> simp
  · intro h; simpa using congrFun h 0
end GlobalTheory.UTrans
