-- Prove2me | solution 1 for GlobalTheory.T.exists_ideal_section_integralFiniteIdele_upToUnits
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:08:02.896533+00:00
-- url     : https://prove2.me/submissions/264d09b4-2a19-4515-a35d-4a0e966a3b85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnits
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIdealSectionIntegralFiniteIdeleUpToUnitsStatement
import Theorems.Thm_GlobalTheory_CMVal_exists_idele_section_of_ideal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.CMVal.Euler
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (E : Type) [Field E] [NumberField E] , ∃ g : Ideal (𝓞 E) → (Af E)ˣ, ∀ y : (Af E)ˣ, (∀ w, Valued.v ((y : Af E) w) ≤ 1) → ∃ J : Ideal (𝓞 E), modF y = ((Ideal.absNorm J : ℕ) : ℝ)⁻¹ ∧ ∀ w, Valued.v ((((g J)⁻¹ * y : (Af E)ˣ) : Af E) w) = 1 := by
  first | exact @GlobalTheory.CMVal.exists_idele_section_of_ideal | exact GlobalTheory.CMVal.exists_idele_section_of_ideal | (intros; apply GlobalTheory.CMVal.exists_idele_section_of_ideal <;> assumption)
end _root_.GlobalTheory.T
