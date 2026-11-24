-- Prove2me | solution 1 for GlobalTheory.ratCircleChar_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:30:40.908185+00:00
-- url     : https://prove2.me/submissions/5822a5de-fa98-4278-8712-2786d560f1fe

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsRepresentativesQuotientRangeMulVecLin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Matrix
open GlobalTheory
variable {A : Type*} [AddCommGroup A] [Fintype A]
namespace GlobalTheory
theorem _root_.solution {x : AddCircle (1 : ℚ)} : ratCircleChar x = 1 ↔ x = 0 := by
  refine ⟨fun h => ?_, fun h => by simp [h]⟩
  induction x using QuotientAddGroup.induction_on with | H r => ?_
  rw [ratCircleChar_coe, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  rw [mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero] at hn
  refine (AddCircle.coe_eq_zero_iff _).2 ⟨n, ?_⟩
  rw [zsmul_eq_mul, mul_one]
  exact_mod_cast hn.symm
end GlobalTheory
