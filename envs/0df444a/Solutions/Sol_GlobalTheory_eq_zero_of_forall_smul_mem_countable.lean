-- Prove2me | solution 1 for GlobalTheory.eq_zero_of_forall_smul_mem_countable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T13:32:22.357423+00:00
-- url     : https://prove2.me/submissions/cc274365-aee0-46fb-9d1e-99c97e13d58d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ArchimedeanThetaValues_DegeneratingToriPeriodMapEqBaseOfYEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_TorusProjPeriodZeroEqReal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_SmulPeriodMapMkZeroFstEqNegForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Set V}
    (hS : S.Countable) {z : V} (hz : ∀ s : ℂ, s • z ∈ S) : z = 0 := by
  by_contra h
  have hinj : Function.Injective fun s : ℂ => s • z := smul_left_injective ℂ h
  have h1 : (Set.univ : Set ℂ).Countable :=
    (hS.preimage_of_injOn hinj.injOn).mono fun s _ => hz s
  exact not_countable_complex h1
end GlobalTheory
