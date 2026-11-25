-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.not_isValChar_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:29:07.253829+00:00
-- url     : https://prove2.me/submissions/cb009eb7-413f-4dc3-8c41-9edd1ab827a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_exists_ramified

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Model
theorem _root_.solution {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q : Finset (HeightOneSpectrum (OF E))} (hf : IsBaseCond 𝔣) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) :
    ¬ IsValChar φ s κ 𝔣 Q (1 : HChar E) := fun h => by
  obtain ⟨P, hP⟩ := exists_ramified hf hQ h
  exact hP (fun _ _ => rfl)
end GlobalTheory.CMVal.Model
