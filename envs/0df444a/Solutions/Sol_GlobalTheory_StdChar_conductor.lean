-- Prove2me | solution 1 for GlobalTheory.StdChar.conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:58:45.873403+00:00
-- url     : https://prove2.me/submissions/8b6b9931-19c3-4766-ba17-c7a5f7e6f141

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticIntegralTraceFormPerfectStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.StdChar
variable {F : Type} [NontriviallyNormedField F]
namespace GlobalTheory.StdChar
theorem _root_.solution [IsUltrametricDist F] {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : F) :
    (∀ e : F, ‖e‖ ≤ 1 → ψ (e * y) = 1) ↔ ‖y‖ ≤ 1 := by
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy y⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy)
      rwa [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul] at this
    apply hx
    have := h (x * y⁻¹) (by rw [norm_mul, norm_inv, mul_inv_le_iff₀ hypos, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one] at this
  · intro hy e he
    exact hψ.1 _ (by rw [norm_mul]; exact mul_le_one₀ he (norm_nonneg _) hy)
end GlobalTheory.StdChar
