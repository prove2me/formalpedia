-- Prove2me | solution 1 for GlobalTheory.CMVal.InhabK.exists_isValChar_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:32:24.54678+00:00
-- url     : https://prove2.me/submissions/f3de7b2b-8df6-4b48-9570-df280d927524

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_InhabK_isCMType_places
import Theorems.Thm_GlobalTheory_CMVal_InhabK_expIn_pow
import Theorems.Thm_GlobalTheory_CMVal_InhabK_exists_over
import Theorems.Thm_GlobalTheory_CMVal_InhabK_exists_place
import Theorems.Thm_GlobalTheory_CMVal_InhabK_isBaseCond_pow
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_isValChar
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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK
namespace GlobalTheory.CMVal.InhabK
theorem _root_.solution (s : ℕ) (κ : InfinitePlace K → ℕ) :
    ∃ v : HeightOneSpectrum (OF K), IsBaseCond (v.asIdeal ^ 2) ∧ ∃ χ : HChar K,
      IsValChar (fun w : InfinitePlace K => w.embedding) s κ (v.asIdeal ^ 2) ∅ χ ∧ ∃ P, ¬ χ.UnrAt P := by
  obtain ⟨v, hv⟩ := exists_place
  have hb := (isBaseCond_pow v hv 2).2 (Or.inr rfl)
  obtain ⟨χ, hχ⟩ := ValEx.exists_isValChar K _ isCMType_places s κ v hb
  obtain ⟨P, hP⟩ := exists_over v
  refine ⟨v, hb, χ, hχ, P, fun hu => ?_⟩
  have h := (hχ.2.2.2 v P hP).2 (Finset.notMem_empty v)
  rw [expIn_pow] at h
  have h0 := (h 0).1 (((expAt_zero_iff χ P).2 hu 0).2 le_rfl)
  omega
end GlobalTheory.CMVal.InhabK
