-- Prove2me | solution 1 for GlobalTheory.CMVal.Euler.one_sub_omega_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T14:00:03.46469+00:00
-- url     : https://prove2.me/submissions/0abc19d7-1010-42c4-b85d-5164ec2220ac

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ValIotaLeOfMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ForallLocInShift
import Theorems.Thm_GlobalTheory_CMVal_Euler_norm_omega
import Theorems.Thm_GlobalTheory_CMVal_modF_unifAt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal Filter Topology
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Euler
variable {E : Type} [Field E] [NumberField E]
namespace GlobalTheory.CMVal.Euler
theorem _root_.solution {χ : HChar E} (h : IsUnitary χ) {S : ℂ} (hS : 0 < S.re) (w : HeightOneSpectrum (𝓞 E)) :
    1 - omega χ S (unifAt w) ≠ 0 := by
  intro h0
  have h1 := norm_omega h S (unifAt w)
  rw [← sub_eq_zero.1 h0, norm_one, modF_unifAt] at h1
  have h2 : (1 : ℝ) < ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) := by exact_mod_cast NumberField.HeightOneSpectrum.one_lt_absNorm w
  exact (Real.rpow_lt_one (by positivity) (inv_lt_one_of_one_lt₀ h2) hS).ne' h1
end GlobalTheory.CMVal.Euler
