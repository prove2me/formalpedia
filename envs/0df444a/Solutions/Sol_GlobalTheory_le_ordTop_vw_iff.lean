-- Prove2me | solution 1 for GlobalTheory.le_ordTop_vw_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:47:11.523658+00:00
-- url     : https://prove2.me/submissions/a6b37d89-f990-45ae-8cbf-80558d64bff4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisKaehlerOfAlgebraicIndependent
import Theorems.Thm_P2M_GlobalTheory_formMap__Multi_014b852379ac
import Theorems.Thm_GlobalTheory_dlogWedge_empty
import Theorems.Thm_GlobalTheory_ordTop_vw_zero
import Theorems.Thm_GlobalTheory_ordTop_vw_unit_mul_zpow
import Theorems.Thm_GlobalTheory_exists_eq_unit_mul_zpow
import Theorems.Thm_GlobalTheory_altRestrictScalars_apply
import Theorems.Thm_GlobalTheory_jacAlt_apply
import Theorems.Thm_P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
import Theorems.Thm_P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.altRestrictScalars_apply
attribute [local simp] GlobalTheory.jacAlt_apply
attribute [local simp] P2M_GlobalTheory_exteriorPowerMapOver__Multi_e236a206a98b
attribute [local simp] P2M_GlobalTheory_wedgeContract__Multi_3b1ba66efe15


attribute [local simp] GlobalTheory.formMap_ιMulti
attribute [local simp] GlobalTheory.dlogWedge_empty
attribute [local simp] GlobalTheory.ordTop_vw_zero

set_option autoImplicit false
open GlobalTheory
open scoped BigOperators TensorProduct nonZeroDivisors
open Module KaehlerDifferential IsLocalRing
variable (V : Type*) {F : Type*} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field F]
  [Algebra V F] [IsFractionRing V F]
variable {V}
namespace GlobalTheory
theorem _root_.solution {t : V} (ht : Irreducible t) (m : ℤ) (f : F) :
    (m : WithTop ℤ) ≤ ordTop_vw V f ↔ ∃ a : V, f = algebraMap V F t ^ m * algebraMap V F a := by
  have h₀ : algebraMap V F t ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V F)).mpr ht.ne_zero
  constructor
  · intro h
    by_cases hf : f = 0
    · exact ⟨0, by simp [hf]⟩
    obtain ⟨k, u, rfl⟩ := exists_eq_unit_mul_zpow ht hf
    rw [ordTop_vw_unit_mul_zpow ht, WithTop.coe_le_coe] at h
    obtain ⟨d, rfl⟩ := Int.le.dest h
    exact ⟨u * t ^ d, by rw [zpow_add₀ h₀, map_mul, map_pow, zpow_natCast]; ring⟩
  · rintro ⟨a, rfl⟩
    by_cases ha : a = 0
    · simp [ha]
    obtain ⟨d, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha ht
    have : algebraMap V F t ^ m * algebraMap V F (u * t ^ d)
        = algebraMap V F u * algebraMap V F t ^ (m + d) := by
      rw [zpow_add₀ h₀, map_mul, map_pow, zpow_natCast]; ring
    rw [this, ordTop_vw_unit_mul_zpow ht, WithTop.coe_le_coe]
    omega
end GlobalTheory
