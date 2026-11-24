-- Prove2me | solution 1 for GlobalTheory.QNorm.mem_normSub_of_isSquare
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T16:27:47.395568+00:00
-- url     : https://prove2.me/submissions/175ee703-3c4d-4ad0-9df4-17b01670642b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTopStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsSquareOfSUnitLocalSquareFiniteRealPlaces
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_QNorm_mem_normSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm
namespace GlobalTheory.QNorm
theorem _root_.solution {F L : Type} [Field F] [CharZero F] [Field L] (φ : F →+* L)
    (δ : Fˣ) (h : IsSquare (φ (δ : F))) (x : Fˣ) : x ∈ normSub φ (δ : F) := by
  obtain ⟨c, hc⟩ := h
  have hδ : φ (δ : F) ≠ 0 := (map_ne_zero φ).mpr δ.ne_zero
  have hc0 : c ≠ 0 := by
    rintro rfl
    simp only [mul_zero] at hc
    exact hδ hc
  have h2 : (2 : L) ≠ 0 := by
    have : φ 2 ≠ 0 := (map_ne_zero φ).mpr two_ne_zero
    rwa [map_ofNat] at this
  rw [mem_normSub]
  refine ⟨(φ (x : F) + 1) / 2, (φ (x : F) - 1) / (2 * c), ?_⟩
  rw [hc]
  field_simp
  ring
end GlobalTheory.QNorm
