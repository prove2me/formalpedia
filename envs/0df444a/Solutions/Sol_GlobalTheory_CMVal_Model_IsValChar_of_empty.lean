-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.IsValChar.of_empty
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:05:33.357742+00:00
-- url     : https://prove2.me/submissions/df27945b-a1cf-4700-9ecb-1043a15624a8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_expIn_eq_zero
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
    {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q) (h : IsValChar φ s κ 𝔣 ∅ χ) :
    IsValChar φ s κ 𝔣 Q χ := by
  refine ⟨h.1, h.2.1, h.2.2.1, fun v P hP => ⟨fun hv => ?_, fun _ => (h.2.2.2 v P hP).2 (by simp)⟩⟩
  have := (h.2.2.2 v P hP).2 (by simp) 1
  rw [expIn_eq_zero.2 (hQ v hv).2] at this
  exact this.2 (by norm_num)
end IsValChar
end GlobalTheory.CMVal.Model
