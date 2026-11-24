-- Prove2me | solution 1 for GlobalTheory.EtaChar.sq_iff_even
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:36.035077+00:00
-- url     : https://prove2.me/submissions/395f055b-9611-493c-93df-caeb481ba114

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadraticStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedValuationParitySignCharacterKernelNorm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.EtaChar
namespace GlobalTheory.EtaChar
theorem _root_.solution {F : Type} [NormedField F] {π : F} (h0 : 0 < ‖π‖) (h1 : ‖π‖ < 1)
    (hall : ∀ x : F, x ≠ 0 → ∃ k : ℤ, ‖x‖ = ‖π‖ ^ k) {x : F} {k : ℤ} (hk : ‖x‖ = ‖π‖ ^ k) :
    (∃ y : F, ‖x‖ = ‖y‖ ^ 2) ↔ Even k := by
  constructor
  · rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := by
      rintro rfl
      have : ‖x‖ = 0 := by simpa using hy
      rw [hk] at this
      exact (zpow_pos h0 k).ne' this
    obtain ⟨j, hj⟩ := hall y hy0
    rw [hk, hj, ← zpow_natCast, ← _root_.zpow_mul] at hy
    have := zpow_right_injective₀ h0 h1.ne hy
    exact ⟨j, by rw [this]; push_cast; ring⟩
  · rintro ⟨j, rfl⟩
    refine ⟨π ^ j, ?_⟩
    rw [hk, norm_zpow, ← zpow_natCast, ← _root_.zpow_mul]
    congr 1
    push_cast; ring
end GlobalTheory.EtaChar
