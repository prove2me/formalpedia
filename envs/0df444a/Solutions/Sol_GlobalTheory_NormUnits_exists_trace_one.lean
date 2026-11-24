-- Prove2me | solution 1 for GlobalTheory.NormUnits.exists_trace_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:30:23.584653+00:00
-- url     : https://prove2.me/submissions/45430fa1-ad05-4a80-9ad9-bafe535aa73f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_TotalDegreeCMulXMulX
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsMulStarEqOfNormOneUnramifiedQuadratic
import Theorems.Thm_P2M_GlobalTheory_NormUnits_norm_sub_le_max__752f971280ab
import Theorems.Thm_GlobalTheory_NormUnits_exists_sqrt_mod


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
    [StarRing E] [hU : Unram F E] (ζ : E) (hζ1 : ‖ζ‖ = 1) (hζ : ∀ b : F, 1 ≤ ‖ζ - algebraMap F E b‖)
    (s t : F) (hs : algebraMap F E s = ζ + star ζ) (ht : algebraMap F E t = ζ * star ζ) :
    ∃ e : E, ‖e‖ ≤ 1 ∧ e + star e = 1 := by
  haveI : IsUltrametricDist E := hU.ultraE
  haveI : IsUltrametricDist F := hU.ultraF
  haveI : LocallyCompactSpace F := hU.lcF
  have hns : ‖star ζ‖ = 1 := by rw [hU.norm_star, hζ1]
  have hdiff : ‖ζ - star ζ‖ = 1 := by
    refine le_antisymm ((norm_sub_le_max' _ _).trans (by rw [hns, hζ1, max_self])) (not_lt.1 fun hlt => ?_)
    have h2le : ‖(2 : F)‖ ≤ 1 := by
      rw [← one_add_one_eq_two]; exact (IsUltrametricDist.norm_add_le_max _ _).trans (by simp)
    have h2E : ‖(2 : E)‖ = ‖(2 : F)‖ := by rw [← map_ofNat (algebraMap F E) 2, norm_algebraMap']
    rcases h2le.lt_or_eq with h2n | h2n
    · have htn : ‖t‖ ≤ 1 := by rw [← norm_algebraMap' E t, ht, norm_mul, hζ1, hns, one_mul]
      obtain ⟨r, hr1, hr⟩ := exists_sqrt_mod F t htn h2n
      have hζr : ‖ζ - algebraMap F E r‖ ≤ 1 :=
        (norm_sub_le_max' _ _).trans (max_le hζ1.le (by rw [norm_algebraMap']; exact hr1))
      have e1 : (ζ - algebraMap F E r) ^ 2 = ζ * (ζ - star ζ) + algebraMap F E (t - r ^ 2) -
          2 * algebraMap F E r * (ζ - algebraMap F E r) := by
        rw [map_sub, map_pow, ht]; ring
      have hA : ‖ζ * (ζ - star ζ)‖ < 1 := by rw [norm_mul, hζ1, one_mul]; exact hlt
      have hB : ‖algebraMap F E (t - r ^ 2)‖ < 1 := by rw [norm_algebraMap', norm_sub_rev]; exact hr
      have hC : ‖2 * algebraMap F E r * (ζ - algebraMap F E r)‖ < 1 := by
        rw [norm_mul, norm_mul, h2E, norm_algebraMap']
        calc ‖(2 : F)‖ * ‖r‖ * ‖ζ - algebraMap F E r‖ ≤ ‖(2 : F)‖ * 1 * 1 := by gcongr
          _ < 1 := by simpa using h2n
      have hsq : ‖ζ - algebraMap F E r‖ ^ 2 < 1 := by
        rw [← norm_pow, e1]
        exact (norm_sub_le_max' _ _).trans_lt
          (max_lt ((IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hA hB)) hC)
      have := hζ r
      nlinarith [norm_nonneg (ζ - algebraMap F E r)]
    · have h2E1 : ‖(2 : E)‖ = 1 := h2E.trans h2n
      have h2ne : (2 : E) ≠ 0 := by intro h; rw [h, norm_zero] at h2E1; exact zero_ne_one h2E1
      have e1 : ζ - algebraMap F E (s / 2) = (ζ - star ζ) / 2 := by
        rw [map_div₀, hs, map_ofNat]; field_simp; ring
      have := hζ (s / 2)
      rw [e1, norm_div, h2E1, div_one] at this
      linarith
  have hne : ζ - star ζ ≠ 0 := by intro h; rw [h, norm_zero] at hdiff; exact zero_ne_one hdiff
  have hne' : star ζ - ζ ≠ 0 := by rw [← neg_sub]; exact neg_ne_zero.2 hne
  refine ⟨ζ / (ζ - star ζ), by rw [norm_div, hζ1, hdiff, div_one], ?_⟩
  rw [star_div₀, star_sub, star_star]
  field_simp
  ring
end GlobalTheory.NormUnits
