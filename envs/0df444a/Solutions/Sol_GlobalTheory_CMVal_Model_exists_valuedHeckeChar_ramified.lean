-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.exists_valuedHeckeChar_ramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:30:24.204881+00:00
-- url     : https://prove2.me/submissions/07509296-23b4-45ed-90d7-2b4dc826ba00

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
import Theorems.Thm_GlobalTheory_CMVal_Model_isCMType_places
import Theorems.Thm_GlobalTheory_CMVal_Model_exists_ramified
import Theorems.Thm_GlobalTheory_CMVal_Model_IsValChar_of_empty
import Theorems.Thm_GlobalTheory_CMVal_Model_exists_place
import Theorems.Thm_GlobalTheory_CMVal_Model_isBaseCond_pow
import Theorems.Thm_P2M_GlobalTheory_CMVal_Model_splits_of_mem__40e3e115741c
import Theorems.Thm_P2M_GlobalTheory_CMVal_Model_exists_place__00af12d7f4b9
import Theorems.Thm_GlobalTheory_CMVal_ValEx_exists_isValChar


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
namespace GlobalTheory.CMVal.Model
theorem _root_.solution (s : ℕ) (κ : InfinitePlace K → ℕ) :
    ∃ v q : HeightOneSpectrum (OF K), IsBaseCond (v.asIdeal ^ 2) ∧ IsFinSetSplitPlacesCoprimeConductor (v.asIdeal ^ 2) {q} ∧ ∃ χ : HChar K,
      IsValChar (fun w : InfinitePlace K => w.embedding) s κ (v.asIdeal ^ 2) {q} χ ∧ ∃ P, ¬ UnrAt χ P := by
  obtain ⟨v, hv⟩ := exists_place
  obtain ⟨q, hq⟩ := exists_place'
  have hb := (isBaseCond_pow v hv 2).2 (Or.inr rfl)
  have hQ : IsFinSetSplitPlacesCoprimeConductor (v.asIdeal ^ 2) {q} := fun w hw => by
    rw [Finset.mem_singleton.1 hw]
    refine ⟨splits_of_mem' q hq, fun hd => q.isPrime.ne_top ?_⟩
    have h43 : ((43 : ℕ) : OF K) ∈ q.asIdeal := Ideal.dvd_iff_le.1 (q.prime.dvd_of_dvd_pow hd) hv
    rw [Ideal.eq_top_iff_one]
    have e : (1 : OF K) = 65 * ((43 : ℕ) : OF K) - 22 * ((127 : ℕ) : OF K) := by push_cast; norm_num
    rw [e]
    exact q.asIdeal.sub_mem (q.asIdeal.mul_mem_left _ h43) (q.asIdeal.mul_mem_left _ hq)
  obtain ⟨χ, hχ⟩ := ValEx.exists_isValChar K _ isCMType_places s κ v hb
  exact ⟨v, q, hb, hQ, χ, IsValChar.of_empty hQ hχ, exists_ramified hb hQ (IsValChar.of_empty hQ hχ)⟩
end GlobalTheory.CMVal.Model
