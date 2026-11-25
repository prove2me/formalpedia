-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.exists_isValChar_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:18.421948+00:00
-- url     : https://prove2.me/submissions/e33af0ba-4f18-43c9-a580-e30f67974f06

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_isCMType_places
import Theorems.Thm_GlobalTheory_CMVal_Model_exists_ramified
import Theorems.Thm_GlobalTheory_CMVal_Model_exists_place
import Theorems.Thm_GlobalTheory_CMVal_Model_isBaseCond_pow
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_isValChar
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
namespace GlobalTheory.CMVal.Model
theorem _root_.solution (s : ℕ) (κ : InfinitePlace K → ℕ) :
    ∃ v : HeightOneSpectrum (OF K), IsBaseCond (v.asIdeal ^ 2) ∧ IsFinSetSplitPlacesCoprimeConductor (v.asIdeal ^ 2) ∅ ∧ ∃ χ : HChar K,
      IsValChar (fun w : InfinitePlace K => w.embedding) s κ (v.asIdeal ^ 2) ∅ χ ∧ ∃ P, ¬ UnrAt χ P := by
  obtain ⟨v, hv⟩ := exists_place
  have hb := (isBaseCond_pow v hv 2).2 (Or.inr rfl)
  have hQ : IsFinSetSplitPlacesCoprimeConductor (v.asIdeal ^ 2) ∅ := by simp [IsFinSetSplitPlacesCoprimeConductor]
  obtain ⟨χ, hχ⟩ := ValEx.exists_isValChar K _ isCMType_places s κ v hb
  exact ⟨v, hb, hQ, χ, hχ, exists_ramified hb hQ hχ⟩
end GlobalTheory.CMVal.Model
