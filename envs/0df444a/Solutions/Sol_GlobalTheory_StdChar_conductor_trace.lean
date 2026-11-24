-- Prove2me | solution 1 for GlobalTheory.StdChar.conductor_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:58:10.982559+00:00
-- url     : https://prove2.me/submissions/a27dd6c9-e5d3-4056-a032-da64cfe41360

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
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
namespace GlobalTheory.StdChar
theorem _root_.solution [hU : Unram F E]
    (htr : ∀ y : E, algebraMap F E (Algebra.trace F E y) = y + star y)
    (he : ∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1)
    {ψ : AddChar F ℂ} (hψ : IsStdChar ψ) (y : E) :
    (∀ e : E, ‖e‖ ≤ 1 → ψ (Algebra.trace F E (e * y)) = 1) ↔ ‖y‖ ≤ 1 := by
  haveI := hU.ultraE
  constructor
  · intro h
    by_contra hy
    push_neg at hy
    obtain ⟨x, hx, hxy⟩ := hψ.2
    obtain ⟨e₀, he₀, hsum⟩ := he
    obtain ⟨a, ha⟩ := hU.unram y
    have hy0 : y ≠ 0 := by rintro rfl; simp at hy; linarith
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    have ha1 : 1 < ‖a‖ := ha ▸ hy
    have ha0 : a ≠ 0 := by rintro rfl; simp at ha1; linarith
    have hxle : ‖x‖ ≤ ‖y‖ := by
      have := hxy a⁻¹ (by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ ha1)
      rw [norm_mul, norm_inv, mul_inv_le_iff₀ (norm_pos_iff.2 ha0), one_mul] at this
      rwa [ha]
    have htr1 : Algebra.trace F E e₀ = 1 := by
      apply (algebraMap F E).injective
      rw [htr, hsum, map_one]
    apply hx
    have := h (algebraMap F E x * e₀ * y⁻¹) (by
      rw [norm_mul, norm_mul, norm_inv, norm_algebraMap', mul_inv_le_iff₀ hypos]
      calc ‖x‖ * ‖e₀‖ ≤ ‖x‖ * 1 := mul_le_mul_of_nonneg_left he₀ (norm_nonneg _)
        _ ≤ 1 * ‖y‖ := by rw [mul_one, one_mul]; exact hxle)
    rwa [mul_assoc, inv_mul_cancel₀ hy0, mul_one, ← Algebra.smul_def, LinearMap.map_smul, htr1,
      smul_eq_mul, mul_one] at this
  · intro hy e he'
    apply hψ.1
    have hz : ‖e * y‖ ≤ 1 := by rw [norm_mul]; exact mul_le_one₀ he' (norm_nonneg _) hy
    rw [← norm_algebraMap' E, htr]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hz (by rw [hU.norm_star]; exact hz))
end GlobalTheory.StdChar
