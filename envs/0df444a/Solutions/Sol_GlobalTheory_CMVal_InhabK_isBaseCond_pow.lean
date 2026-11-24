-- Prove2me | solution 1 for GlobalTheory.CMVal.InhabK.isBaseCond_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:37:06.030598+00:00
-- url     : https://prove2.me/submissions/14e4d3d1-c5e0-4894-a5e4-06c1302db601

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor
import Theorems.Thm_GlobalTheory_CMVal_InhabK_expIn_pow
import Theorems.Thm_GlobalTheory_CMVal_InhabK_absNorm_of_mem
import Theorems.Thm_GlobalTheory_CMVal_InhabK_not_dvd_discr
import Theorems.Thm_GlobalTheory_CMVal_InhabK_splits_of_mem
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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK
namespace GlobalTheory.CMVal.InhabK
theorem _root_.solution (v : HeightOneSpectrum (OF K)) (h : ((43 : ℕ) : OF K) ∈ v.asIdeal) (n : ℕ) :
    IsBaseCond (v.asIdeal ^ n) ↔ n = 1 ∨ n = 2 := by
  constructor
  · rintro ⟨-, h1, h2⟩
    have hn : n ≠ 0 := by rintro rfl; exact h1 (by simp)
    have := (h2 v (dvd_pow_self _ hn)).2.1
    rw [expIn_pow] at this
    omega
  · intro hn
    have hn0 : n ≠ 0 := by omega
    refine ⟨pow_ne_zero _ v.ne_bot, fun e => v.isPrime.ne_top ?_, fun w hw => ?_⟩
    · exact top_le_iff.1 (e ▸ Ideal.pow_le_self hn0)
    · have hwv : w = v := by
        have := Ideal.dvd_iff_le.1 (w.prime.dvd_of_dvd_pow hw)
        exact HeightOneSpectrum.ext (v.isMaximal.eq_of_le w.isPrime.ne_top this).symm
      subst hwv
      refine ⟨splits_of_mem w h, by rw [expIn_pow]; omega, 43, by norm_num, by norm_num, h, not_dvd_discr, absNorm_of_mem⟩
end GlobalTheory.CMVal.InhabK
