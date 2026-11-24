-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.inhabited_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:37:51.114588+00:00
-- url     : https://prove2.me/submissions/8ec78d40-53a6-4129-9960-2fefddba998e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_isCMType_places
import Theorems.Thm_GlobalTheory_CMVal_Model_unramFin_K
import Theorems.Thm_GlobalTheory_CMVal_Model_splits_of_mem
import Theorems.Thm_GlobalTheory_CMVal_Model_exists_place
import Theorems.Thm_GlobalTheory_CMVal_Model_isBaseCond_pow
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
theorem _root_.solution : UnramFin K ∧ IsCMType (fun w : InfinitePlace K => w.embedding) ∧
    ∃ v : HeightOneSpectrum (OF K), Splits v ∧ IsBaseCond v.asIdeal ∧ IsBaseCond (v.asIdeal ^ 2) ∧
      ¬ IsBaseCond (v.asIdeal ^ 3) ∧ IsFinSetSplitPlacesCoprimeConductor v.asIdeal ∅ ∧ ¬ IsFinSetSplitPlacesCoprimeConductor v.asIdeal {v} ∧ IsFinSetSplitPlacesCoprimeConductor ⊤ {v} := by
  obtain ⟨v, hv⟩ := exists_place
  refine ⟨unramFin_K, isCMType_places, v, splits_of_mem v hv, ?_, (isBaseCond_pow v hv 2).2 (Or.inr rfl), ?_, by simp [IsFinSetSplitPlacesCoprimeConductor],
    fun h => (h v (by simp)).2 dvd_rfl, fun q hq => ?_⟩
  · simpa using (isBaseCond_pow v hv 1).2 (Or.inl rfl)
  · rw [isBaseCond_pow v hv]; omega
  · rw [Finset.mem_singleton.1 hq]
    exact ⟨splits_of_mem v hv, fun h => v.isPrime.ne_top (by rwa [Ideal.dvd_iff_le, top_le_iff] at h)⟩
end GlobalTheory.CMVal.Model
