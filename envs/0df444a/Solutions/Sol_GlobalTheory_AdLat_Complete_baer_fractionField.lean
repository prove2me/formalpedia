-- Prove2me | solution 1 for GlobalTheory.AdLat.Complete.baer_fractionField
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:41:12.442772+00:00
-- url     : https://prove2.me/submissions/0ef0da9d-6ab4-436c-8977-86d384c721b2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_SmulBasisMemHatIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IntegralFiniteAdeleCompleteSeparated
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionLatticeSeparatedComplete
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Complete
namespace GlobalTheory.AdLat.Complete
theorem _root_.solution (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] : Module.Baer R K := by
  intro I g
  by_cases hI : ∃ a ∈ I, a ≠ 0
  · obtain ⟨a, ha, ha0⟩ := hI
    have ha' : algebraMap R K a ≠ 0 := by
      simpa using ha0
    refine ⟨LinearMap.toSpanSingleton R K (g ⟨a, ha⟩ / algebraMap R K a), fun x hx => ?_⟩
    have h : a • g ⟨x, hx⟩ = x • g ⟨a, ha⟩ := by
      rw [← map_smul, ← map_smul]
      congr 1
      ext
      simp [mul_comm]
    rw [LinearMap.toSpanSingleton_apply, Algebra.smul_def]
    rw [Algebra.smul_def, Algebra.smul_def] at h
    field_simp
    rw [← h]
  · refine ⟨0, fun x hx => ?_⟩
    have : x = 0 := by
      by_contra h
      exact hI ⟨x, hx, h⟩
    subst this
    have : (⟨0, hx⟩ : I) = 0 := rfl
    rw [this, map_zero, map_zero]
end GlobalTheory.AdLat.Complete
