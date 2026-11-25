-- Prove2me | solution 1 for GlobalTheory.MomN.latInt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:30.907939+00:00
-- url     : https://prove2.me/submissions/f78f06e9-d096-4296-9061-d7b6eb80bde9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LatIntZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.MomN
open GlobalTheory.MomOne
variable {q : ℕ} [Fact q.Prime] {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace GlobalTheory.MomN
theorem _root_.solution (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) (Λ : AddSubgroup V) : LatInt ι ω Λ (fun _ => 1) := by
  intro κ _ v _
  refine ⟨ContinuousMap.evalCLM ℂ_[q] 0, ?_, ?_⟩
  · refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
    rw [one_mul]
    exact f.norm_coe_le_norm 0
  · intro k j f hf
    rw [ContinuousMap.evalCLM_apply, hf]
    cases k with
    | zero => simp
    | succ k =>
      rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero k), Finset.prod_eq_zero (Finset.mem_univ 0)]
      · simp
      · simp [zc]
end GlobalTheory.MomN
