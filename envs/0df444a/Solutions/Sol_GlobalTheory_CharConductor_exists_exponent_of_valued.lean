-- Prove2me | solution 1 for GlobalTheory.CharConductor.exists_exponent_of_valued
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T14:35:42.498653+00:00
-- url     : https://prove2.me/submissions/de9f554b-05d1-490f-9cec-17b9bcc7e06e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfNormSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsConductorAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Theorems.Thm_GlobalTheory_CharacterConductorBall_exists_conductor
import Theorems.Thm_GlobalTheory_ConductorAdicCompletion_exists_conductor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CharConductor
namespace GlobalTheory.CharConductor
theorem _root_.solution {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | exact _root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | (apply _root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> assumption)
  | (intros; apply _root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CharacterConductorBall.exists_conductor ..)
end GlobalTheory.CharConductor
