-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.IsValChar.unrAt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:35:38.182839+00:00
-- url     : https://prove2.me/submissions/1a8eb5cc-4b74-4e79-a56a-2a2bb5e4f788

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_expIn_eq_zero
import Theorems.Thm_GlobalTheory_CMVal_Model_expAt_zero_iff
import Theorems.Thm_GlobalTheory_CMVal_expAt_zero_iff


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
namespace IsValChar
theorem _root_.solution {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (h : IsValChar φ s κ 𝔣 Q χ)
    {v : HeightOneSpectrum (OF E)} {P : HeightOneSpectrum (𝓞 E)} (hP : Over P v) (hQ : v ∉ Q) (hf : ¬ v.asIdeal ∣ 𝔣) :
    UnrAt χ P := by
  have := (h.2.2.2 v P hP).2 hQ
  rwa [expIn_eq_zero.2 hf, expAt_zero_iff] at this
end IsValChar
end GlobalTheory.CMVal.Model
