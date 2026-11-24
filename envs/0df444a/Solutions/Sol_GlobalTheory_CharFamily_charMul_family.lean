-- Prove2me | solution 1 for GlobalTheory.CharFamily.charMul_family
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:26:21.421969+00:00
-- url     : https://prove2.me/submissions/e2f5e4c4-abb3-4899-b217-68af0e0cf590

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound
import Theorems.Thm_GlobalTheory_CharFamily_seminorm_mul_le
import Theorems.Thm_GlobalTheory_CharFamily_contDiff_char
import Theorems.Thm_GlobalTheory_CharFamily_norm_iteratedFDeriv_char_le
import Theorems.Thm_GlobalTheory_CharFamily_norm_iteratedFDeriv_char_sub_one_le
import Theorems.Thm_GlobalTheory_CharFamily_one_add_pow_le
import Theorems.Thm_GlobalTheory_CharFormDeriv_hasTemperateGrowth_char


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
open GlobalTheory GlobalTheory.CharFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.CharFamily
theorem _root_.solution : ∀ (E P : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (A : P →L[ℝ] E →L[ℝ] ℝ) (f : SchwartzMap E ℂ), ∃ Φ : P → SchwartzMap E ℂ,
    (∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x) ∧ Continuous Φ ∧
    ∀ k n : ℕ, ∃ C : ℝ, ∀ ξ, SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ C * (1 + ‖ξ‖ ^ n) := by
  intro E P _ _ _ _ A f
  have htg : ∀ L : E →L[ℝ] ℝ,
      Function.HasTemperateGrowth (fun x : E => Complex.exp (I * (L x : ℂ))) := fun L => by
    simpa using GlobalTheory.CharFormDeriv.hasTemperateGrowth_char L 1
  let Φ : P → SchwartzMap E ℂ := fun ξ =>
    SchwartzMap.smulLeftCLM ℂ (fun x : E => Complex.exp (I * (A ξ x : ℂ))) f
  have hΦ : ∀ ξ x, Φ ξ x = Complex.exp (Complex.I * (A ξ x : ℂ)) * f x := fun ξ x => by
    simp only [Φ, SchwartzMap.smulLeftCLM_apply_apply (htg (A ξ)), smul_eq_mul]
  refine ⟨Φ, hΦ, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun ζ => ?_
    unfold ContinuousAt
    rw [(schwartz_withSeminorms ℂ E ℂ).tendsto_nhds Φ (Φ ζ)]
    rintro ⟨k, n⟩ ε hε
    set K := 2 * 2 ^ n * (2 ^ (k + 1) *
      ((Finset.Iic (k + 1, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) (Φ ζ)) with hK
    have hK0 : 0 ≤ K := mul_nonneg (by positivity) (mul_nonneg (by positivity) (apply_nonneg _ _))
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
    set m := min 1 (ε / (K + 1)) with hm
    have hm0 : 0 < m := lt_min one_pos (div_pos hε (by linarith))
    have hδ : 0 < m / (‖A‖ + 1) := div_pos hm0 (by linarith)
    filter_upwards [Metric.ball_mem_nhds ζ hδ] with η hη
    rw [Metric.mem_ball, dist_eq_norm] at hη
    show SchwartzMap.seminorm ℂ k n (Φ η - Φ ζ) < ε
    set L := A (η - ζ) with hLdef
    have hLle : ‖L‖ ≤ ‖A‖ * ‖η - ζ‖ := A.le_opNorm _
    have hLm : ‖L‖ < m := by
      calc ‖L‖ ≤ ‖A‖ * ‖η - ζ‖ := hLle
        _ ≤ (‖A‖ + 1) * ‖η - ζ‖ := by gcongr; linarith
        _ < (‖A‖ + 1) * (m / (‖A‖ + 1)) := by gcongr
        _ = m := by field_simp
    have hL1 : ‖L‖ ≤ 1 := (lt_of_lt_of_le hLm (min_le_left _ _)).le
    have hLε : ‖L‖ < ε / (K + 1) := lt_of_lt_of_le hLm (min_le_right _ _)
    have hpt : ∀ x, (Φ η - Φ ζ) x = (Complex.exp (I * (L x : ℂ)) - 1) * Φ ζ x := fun x => by
      have hs : A η x = L x + A ζ x := by simp [hLdef, map_sub]
      rw [SchwartzMap.sub_apply, hΦ, hΦ, hs]
      push_cast
      rw [mul_add, Complex.exp_add]
      ring
    have hb := seminorm_mul_le (fun x : E => Complex.exp (I * (L x : ℂ)) - 1)
      ((contDiff_char L).sub contDiff_const) (Φ ζ) (Φ η - Φ ζ) hpt k n 1 (2 * ‖L‖)
      (by positivity) (fun i _ x => norm_iteratedFDeriv_char_sub_one_le L hL1 i x)
    calc SchwartzMap.seminorm ℂ k n (Φ η - Φ ζ) ≤ ‖L‖ * K := by rw [hK]; linarith [hb]
      _ ≤ ‖L‖ * (K + 1) := by gcongr; linarith
      _ < ε / (K + 1) * (K + 1) := by gcongr
      _ = ε := by field_simp
  · intro k n
    set S := 2 ^ (k + 0) * ((Finset.Iic (k + 0, n)).sup fun p => SchwartzMap.seminorm ℂ p.1 p.2) f
      with hS
    have hS0 : 0 ≤ S := mul_nonneg (by positivity) (apply_nonneg _ _)
    refine ⟨2 ^ n * ((1 + ‖A‖) ^ n * 2 ^ n) * S, fun ξ => ?_⟩
    have hA0 : 0 ≤ ‖A‖ := norm_nonneg A
    have hξ0 : 0 ≤ ‖ξ‖ := norm_nonneg ξ
    set L := A ξ with hLdef
    have hL0 : 0 ≤ ‖L‖ := norm_nonneg L
    have hb := seminorm_mul_le (fun x : E => Complex.exp (I * (L x : ℂ))) (contDiff_char L) f (Φ ξ)
      (hΦ ξ) k n 0 ((1 + ‖L‖) ^ n) (by positivity) (fun i hi x => by
        rw [pow_zero, mul_one]
        calc _ ≤ ‖L‖ ^ i := norm_iteratedFDeriv_char_le L i x
          _ ≤ (1 + ‖L‖) ^ i := by gcongr; linarith
          _ ≤ (1 + ‖L‖) ^ n := pow_le_pow_right₀ (by linarith) hi)
    have h1 : (1 + ‖L‖) ^ n ≤ (1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n)) := by
      calc (1 + ‖L‖) ^ n ≤ ((1 + ‖A‖) * (1 + ‖ξ‖)) ^ n := by
            gcongr
            have := A.le_opNorm ξ
            nlinarith
        _ = (1 + ‖A‖) ^ n * (1 + ‖ξ‖) ^ n := mul_pow _ _ _
        _ ≤ (1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n)) := by
            gcongr; exact one_add_pow_le _ hξ0 n
    calc SchwartzMap.seminorm ℂ k n (Φ ξ) ≤ 2 ^ n * (1 + ‖L‖) ^ n * S := hb
      _ ≤ 2 ^ n * ((1 + ‖A‖) ^ n * (2 ^ n * (1 + ‖ξ‖ ^ n))) * S := by gcongr
      _ = 2 ^ n * ((1 + ‖A‖) ^ n * 2 ^ n) * S * (1 + ‖ξ‖ ^ n) := by ring
end GlobalTheory.CharFamily
