-- Prove2me | solution 1 for GlobalTheory.CMVal.modF_mul_pos_principal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:52:38.66613+00:00
-- url     : https://prove2.me/submissions/0ceaa195-9b62-465b-bc31-6178ba5836fc

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_modF_mul
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_modF_pos
import Theorems.Thm_GlobalTheory_CMVal_IdeleModule_modF_princ

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
namespace GlobalTheory.CMVal
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E], (∀ y y' : (Af E)ˣ, modF (y * y') = modF y * modF y') ∧ (∀ y : (Af E)ˣ, 0 < modF y) ∧ ∀ k : Eˣ, modF (Units.map (algebraMap E (Af E)).toMonoidHom k) = (|(Algebra.norm ℚ (k : E) : ℝ)|)⁻¹ :=
  fun _ _ _ => ⟨IdeleModule.modF_mul, IdeleModule.modF_pos, IdeleModule.modF_princ⟩
end GlobalTheory.CMVal
