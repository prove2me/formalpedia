-- Prove2me | solution 1 for GlobalTheory.CharConductor.exists_conductor_exponent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:04:31.226715+00:00
-- url     : https://prove2.me/submissions/c8e010a7-cbd3-4a41-b17a-f3014c63c6a7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ImportsTer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_EqOneOfNormSubOneLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsConductorAdicCompletion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_AdditiveCharConductorExists
import Theorems.Thm_GlobalTheory_ConductorAdicCompletion_exists_conductor_adicCompletion


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
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion
  | exact _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion
  | (apply _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion ..)
end GlobalTheory.CharConductor
