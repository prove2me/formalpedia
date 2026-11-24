-- Prove2me | solution 1 for GlobalTheory.CMVal.Model.not_intAt_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:05:25.507677+00:00
-- url     : https://prove2.me/submissions/92dcfbe0-d0b3-4677-854b-3c62d7f92f53

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
namespace GlobalTheory.CMVal.Model
theorem _root_.solution {l : ℕ} (hl : l.Prime) : ¬ IntAt l (l : ℂ)⁻¹ := by
  rintro ⟨n, hn, h⟩
  have e : (n : ℂ) * (l : ℂ)⁻¹ = algebraMap ℚ ℂ ((n : ℚ) * (l : ℚ)⁻¹) := by simp
  rw [e, isIntegral_algebraMap_iff (algebraMap ℚ ℂ).injective] at h
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  have h0 : (l : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hl.ne_zero
  have : (n : ℚ) = l * z := by
    have hz' : (z : ℚ) = n * (l : ℚ)⁻¹ := by simpa using hz
    rw [hz']; field_simp
  have h2 : (n : ℤ) = l * z := by exact_mod_cast this
  have h3 : l ∣ n := Int.natCast_dvd_natCast.1 ⟨z, h2⟩
  exact hl.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hn.symm h3)
end GlobalTheory.CMVal.Model
