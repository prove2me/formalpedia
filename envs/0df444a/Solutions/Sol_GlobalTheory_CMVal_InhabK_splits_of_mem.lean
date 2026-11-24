-- Prove2me | solution 1 for GlobalTheory.CMVal.InhabK.splits_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:20:32.781188+00:00
-- url     : https://prove2.me/submissions/4b027b13-9321-4e60-a327-21dc289f1cd3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_InhabK_exists_over
import Theorems.Thm_GlobalTheory_CMVal_InhabK_splits_of_absNorm
import Theorems.Thm_GlobalTheory_CMVal_InhabK_sub_conj_notMem
import Theorems.Thm_GlobalTheory_CMVal_InhabK_zeta_prim
import Theorems.Thm_GlobalTheory_CMVal_InhabK_absNorm_of_mem

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
theorem _root_.solution (v : HeightOneSpectrum (OF K)) (h : ((43 : ℕ) : OF K) ∈ v.asIdeal) : Splits v := by
  obtain ⟨P, hP⟩ := exists_over v
  refine splits_of_absNorm (by norm_num : Nat.Prime 43) P v hP (absNorm_of_mem P ?_) _
    (sub_conj_notMem zeta_prim P.isPrime.ne_top)
  rw [← hP, Ideal.mem_comap, map_natCast] at h
  exact h
end GlobalTheory.CMVal.InhabK
