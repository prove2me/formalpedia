-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.exists_ramified
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:06:17.709496+00:00
-- url     : https://prove2.me/submissions/97be82db-f315-41c8-bd8a-edd6121b3227

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_expIn_eq_zero
import Theorems.Thm_GlobalTheory_CMVal_Model_exists_over
import Theorems.Thm_Formalism_L2_Host_HChar_unrAt_iff


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
    {Q : Finset (HeightOneSpectrum (OF E))} {χ : HChar E} (hf : IsBaseCond 𝔣) (hQ : IsFinSetSplitPlacesCoprimeConductor 𝔣 Q)
    (h : IsValChar φ s κ 𝔣 Q χ) : ∃ P, ¬ UnrAt χ P := by
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal 𝔣 hf.2.1
  have hne : M ≠ ⊥ := fun e => hf.1 (le_bot_iff.1 (e ▸ hle))
  let v : HeightOneSpectrum (OF E) := ⟨M, hM.isPrime, hne⟩
  have hd : v.asIdeal ∣ 𝔣 := Ideal.dvd_iff_le.2 hle
  obtain ⟨P, hP⟩ := exists_over v
  refine ⟨P, fun hu => ?_⟩
  have h1 := ((h.2.2.2 v P hP).2 (fun hq => (hQ v hq).2 hd) 0).1 ((χ.unrAt_iff P).1 hu)
  exact expIn_eq_zero.1 (Nat.le_zero.1 h1) hd
end GlobalTheory.CMVal.Model
