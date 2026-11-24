-- Prove2me | solution 1 for GlobalTheory.RealWeil.integral_gau_twisted_conv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:50:12.031801+00:00
-- url     : https://prove2.me/submissions/9a87a53c-400b-4927-8711-bbf5e9fcaa1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousFourierGau
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralGauTwistedConv
import Theorems.Thm_GlobalTheory_RealWeil_omJ_skew


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder
open GlobalTheory GlobalTheory.RealWeil
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
  [BorelSpace V] {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] {J : V ≃ₗᵢ[ℝ] V}
namespace GlobalTheory.RealWeil
theorem _root_.solution (hJ : ∀ x, J (J x) = -x) (a y : V) :
    ∫ u, gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ))) = gau a * gau y := by
  set m : V := (1 / 2 : ℝ) • (y - a) with hm
  have hym : y - a = m + m := by
    rw [hm, ← add_smul]; norm_num
  have hself : ∀ x : V, ⟪x, J x⟫ = 0 := by
    intro x
    have := omJ_skew hJ x x
    unfold omJ at this
    linarith
  have hsk : ∀ x z : V, ⟪z, J x⟫ = -⟪x, J z⟫ := fun x z => by
    have := omJ_skew hJ x z
    unfold omJ at this
    exact this
  have hpt : ∀ v : V, gau (v + m) * (gau (y - (v + m + a)) *
      cexp (π * I * ((omJ J (v + m) a + omJ J (v + m + a) y : ℝ) : ℂ))) =
      cexp (-(π : ℂ) * ‖v‖ ^ 2 + (π * I) * ⟪J (a + y), v⟫) * cexp (-(π : ℂ) * ‖m‖ ^ 2) := by
    intro v
    have e1 : y - (v + m + a) = m - v := by
      have hy : y = m + m + a := by rw [← hym]; abel
      rw [hy]; abel
    have h1 : ‖v + m‖ ^ 2 + ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 := by
      rw [e1, norm_add_sq_real, norm_sub_sq_real, real_inner_comm m v]; ring
    have h2 : omJ J (v + m) a + omJ J (v + m + a) y = ⟪J (a + y), v⟫ := by
      unfold omJ
      rw [real_inner_comm v (J (a + y)), hm]
      simp only [map_add, inner_add_left, inner_add_right, real_inner_smul_left, inner_sub_left]
      have h3 := hsk a y
      have h4 := hself a
      have h5 := hself y
      linarith
    have h1c : ((‖y - (v + m + a)‖ : ℝ) : ℂ) ^ 2 =
        2 * (‖v‖ : ℂ) ^ 2 + 2 * (‖m‖ : ℂ) ^ 2 - (‖v + m‖ : ℂ) ^ 2 := by
      have h6 : ‖y - (v + m + a)‖ ^ 2 = 2 * ‖v‖ ^ 2 + 2 * ‖m‖ ^ 2 - ‖v + m‖ ^ 2 := by linarith
      exact_mod_cast h6
    simp only [gau, ← Complex.exp_add]
    congr 1
    rw [h1c, h2]
    ring
  have hshift := integral_add_right_eq_self (μ := (volume : Measure V))
    (fun u => gau u * (gau (y - (u + a)) * cexp (π * I * ((omJ J u a + omJ J (u + a) y : ℝ) : ℂ)))) m
  rw [← hshift]
  simp only [hpt]
  have hb : 0 < (π : ℂ).re := by simpa using Real.pi_pos
  have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [integral_mul_const, GaussianFourier.integral_cexp_neg_mul_sq_norm_add hb, div_self hπ, Complex.one_cpow, one_mul,
    LinearIsometryEquiv.norm_map, gau, gau, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h3 : ‖m‖ ^ 2 = ‖a‖ ^ 2 / 2 + ‖y‖ ^ 2 / 2 - ‖a + y‖ ^ 2 / 4 := by
    rw [hm, norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_pow,
      norm_sub_sq_real, norm_add_sq_real, real_inner_comm y a]
    ring
  have h3c : (‖m‖ : ℂ) ^ 2 = (‖a‖ : ℂ) ^ 2 / 2 + (‖y‖ : ℂ) ^ 2 / 2 - (‖a + y‖ : ℂ) ^ 2 / 4 := by
    exact_mod_cast h3
  rw [h3c, mul_pow, I_sq]
  field_simp
  ring
end GlobalTheory.RealWeil
