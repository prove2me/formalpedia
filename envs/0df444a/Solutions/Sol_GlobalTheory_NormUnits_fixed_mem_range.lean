-- Prove2me | solution 1 for GlobalTheory.NormUnits.fixed_mem_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:40:42.766101+00:00
-- url     : https://prove2.me/submissions/13333719-9d2f-4396-b3b2-54e65ff6c483

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadratic

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
open GlobalTheory GlobalTheory.NormUnits
namespace GlobalTheory.NormUnits
theorem _root_.solution (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (ζ : E) (hζ : ∀ b : F, 1 ≤ ‖ζ - algebraMap F E b‖) :
    ∀ w : E, star w = w → ∃ a : F, algebraMap F E a = w := by
  have hζF : ∀ b : F, algebraMap F E b ≠ ζ := fun b h => by
    have := hζ b; rw [h, sub_self, norm_zero] at this; linarith
  have hli : LinearIndependent F ![(1 : E), ζ] := by
    rw [LinearIndependent.pair_iff]
    intro c d h
    by_cases hd : d = 0
    · subst hd
      rw [zero_smul, add_zero, Algebra.smul_def, mul_one] at h
      exact ⟨(map_eq_zero _).1 h, rfl⟩
    · exfalso
      have hdE : algebraMap F E d ≠ 0 := (map_ne_zero _).2 hd
      apply hζF (-(c / d))
      rw [Algebra.smul_def, Algebra.smul_def, mul_one] at h
      rw [map_neg, map_div₀]
      field_simp
      linear_combination (-1 : E) * h
  let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp [hU.finrank_eq])
  have hB : ⇑B = ![(1 : E), ζ] := coe_basisOfLinearIndependentOfCardEqFinrank _ _
  have hspan : ∀ w : E, ∃ a b : F, algebraMap F E a + algebraMap F E b * ζ = w := by
    intro w
    refine ⟨B.repr w 0, B.repr w 1, ?_⟩
    have := B.sum_repr w
    rw [Fin.sum_univ_two, hB] at this
    simpa [Algebra.smul_def] using this
  have hsζ : star ζ ≠ ζ := by
    intro h
    obtain ⟨y, hy⟩ := hU.star_ne
    obtain ⟨a, b, rfl⟩ := hspan y
    apply hy
    rw [star_add, star_mul, hU.star_fix, hU.star_fix, h, mul_comm]
  intro w hw
  obtain ⟨a, b, rfl⟩ := hspan w
  rw [star_add, star_mul, hU.star_fix, hU.star_fix] at hw
  have h0 : algebraMap F E b * (star ζ - ζ) = 0 := by linear_combination hw
  rcases mul_eq_zero.1 h0 with hb | hb
  · exact ⟨a, by rw [hb, zero_mul, add_zero]⟩
  · exact absurd (sub_eq_zero.1 hb) hsζ
end GlobalTheory.NormUnits
