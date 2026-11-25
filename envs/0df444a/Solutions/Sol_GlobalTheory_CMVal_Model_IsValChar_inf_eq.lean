-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.IsValChar.inf_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:29:54.994001+00:00
-- url     : https://prove2.me/submissions/56fcf345-9756-4645-8269-0ffc8151a9e3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
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
theorem _root_.solution {I : Type} [Fintype I] {φ : I → E →+* ℂ} {s : ℕ} {κ : I → ℕ} {𝔣 : Ideal (OF E)}
    {Q Q' : Finset (HeightOneSpectrum (OF E))} {χ χ' : HChar E} (h : IsValChar φ s κ 𝔣 Q χ) (h' : IsValChar φ s κ 𝔣 Q' χ')
    (k : Eˣ) : (χ * χ'⁻¹).inf k = 1 := by
  have : χ.inf k = χ'.inf k := Units.ext ((h.2.2.1 k).trans (h'.2.2.1 k).symm)
  simp [this]
end IsValChar
end GlobalTheory.CMVal.Model
