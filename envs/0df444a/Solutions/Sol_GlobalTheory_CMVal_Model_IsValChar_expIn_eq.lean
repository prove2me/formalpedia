-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.IsValChar.expIn_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:29:50.771386+00:00
-- url     : https://prove2.me/submissions/6640b2e0-cc12-4377-a7bb-efd3cb99c2b5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_exists_over
import Theorems.Thm_GlobalTheory_CMVal_ExpAt_unique
import Theorems.Thm_GlobalTheory_CMVal_IsHeckeL_unique
import Theorems.Thm_GlobalTheory_CMVal_IsLatSum_unique
import Theorems.Thm_GlobalTheory_CMVal_IsToricSum_unique
import Theorems.Thm_GlobalTheory_CMVal_coe_latticeSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.CMVal.coe_latticeSub



set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Model
namespace IsValChar
theorem _root_.solution {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 𝔤 : Ideal (OF E)}
    {χ : HChar E} (h : IsValChar φ s κ 𝔣 ∅ χ) (h' : IsValChar φ s κ 𝔤 ∅ χ) (v : HeightOneSpectrum (OF E)) :
    expIn 𝔣 v = expIn 𝔤 v := by
  obtain ⟨P, hP⟩ := exists_over v
  exact ((h.2.2.2 v P hP).2 (by simp)).unique ((h'.2.2.2 v P hP).2 (by simp))
end IsValChar
end GlobalTheory.CMVal.Model
