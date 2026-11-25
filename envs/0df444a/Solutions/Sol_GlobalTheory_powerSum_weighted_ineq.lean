-- Prove2me | solution 1 for GlobalTheory.powerSum_weighted_ineq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:04:27.164003+00:00
-- url     : https://prove2.me/submissions/b8fff363-6e35-4f82-9ff2-adc584682b1e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_WeightedFejerPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Theorems.Thm_GlobalTheory_sum_Icc_three_quarters_pow_le
import Theorems.Thm_GlobalTheory_T_neg_one_le_sum_fejer_cos_re_pow_and_lower_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {ι : Type} (S : Finset ι) (z : ι → ℂ) (b : ι → ℕ) (i₀ : ι)
    (L δ x : ℝ) (hi : i₀ ∈ S) (hb : 1 ≤ b i₀) (hL : 1 ≤ L) (hδ : 0 < δ) (hx0 : 0 ≤ x)
    (hx : x ≤ 1 / 2) (hz : 1 / (1 + x) ≤ ‖z i₀‖) (hS : (∑ i ∈ S, (b i : ℝ)) ≤ L)
    (hp : ∀ j : ℕ, 1 ≤ j → (∑ i ∈ S, (b i : ℂ) * z i ^ j).re ≤ 2 * j * δ + L / 2 ^ j) (J : ℕ) :
    (J : ℝ) / 4 - 7 * L ≤ 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by
  classical
  obtain ⟨i₁, hi₁, hmax⟩ := Finset.exists_max_image (S.filter fun i => 1 ≤ b i)
    (fun i => ‖z i‖) ⟨i₀, Finset.mem_filter.2 ⟨hi, hb⟩⟩
  obtain ⟨hi₁S, hb₁⟩ := Finset.mem_filter.1 hi₁
  set R : ℝ := ‖z i₁‖ with hR
  have h1x : 0 < 1 + x := by linarith
  have hRge : 1 / (1 + x) ≤ R := hz.trans (hmax i₀ (Finset.mem_filter.2 ⟨hi, hb⟩))
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity) hRge
  have hRinv : R⁻¹ ≤ 1 + x := by
    rw [inv_le_comm₀ hRpos h1x, ← one_div]; exact hRge
  have hRinv0 : 0 ≤ R⁻¹ := by positivity
  set θ : ℝ := Complex.arg (z i₁) with hθ
  obtain ⟨hF1, hF2⟩ := GlobalTheory.T.neg_one_le_sum_fejer_cos_re_pow_and_lower_bound J θ
  set c : ℕ → ℝ := fun j => (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) with hc
  set F : ℂ → ℝ := fun w => ∑ j ∈ Finset.Icc 1 J, c j * (w ^ j).re with hF
  have hF1' : ∀ w : ℂ, ‖w‖ ≤ 1 → -1 ≤ F w := hF1
  have hF2' : (J : ℝ) / 4 - 3 / 4 ≤ F (Complex.exp (θ * I)) := hF2
  set w : ι → ℂ := fun i => ((R⁻¹ : ℝ) : ℂ) * z i with hw
  have hw₁ : w i₁ = Complex.exp (θ * I) := by
    have h := Complex.norm_mul_exp_arg_mul_I (z i₁)
    have hR' : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
    show ((R⁻¹ : ℝ) : ℂ) * z i₁ = _
    rw [← h]
    push_cast
    rw [← hR, ← hθ, ← mul_assoc, inv_mul_cancel₀ hR', one_mul]
  have hwn : ∀ i ∈ S, 1 ≤ b i → ‖w i‖ ≤ 1 := by
    intro i hiS hbi
    have := hmax i (Finset.mem_filter.2 ⟨hiS, hbi⟩)
    show ‖((R⁻¹ : ℝ) : ℂ) * z i‖ ≤ 1
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hRinv0, inv_mul_le_iff₀ hRpos, mul_one]
    exact this

  have hlow : (J : ℝ) / 4 - L ≤ ∑ i ∈ S, (b i : ℝ) * F (w i) := by
    have hnn : ∀ i ∈ S, 0 ≤ (b i : ℝ) * (F (w i) + 1) := by
      intro i hiS
      rcases Nat.eq_zero_or_pos (b i) with h0 | h0
      · simp [h0]
      · have := hF1' _ (hwn i hiS h0)
        exact mul_nonneg (Nat.cast_nonneg _) (by linarith)
    have h1 := Finset.single_le_sum hnn hi₁S
    have hb1 : (1 : ℝ) ≤ b i₁ := by exact_mod_cast hb₁
    have h2 := hF1' _ (hwn i₁ hi₁S hb₁)
    have h3 : F (w i₁) + 1 ≤ (b i₁ : ℝ) * (F (w i₁) + 1) := by nlinarith
    have h4 : ∑ i ∈ S, (b i : ℝ) * (F (w i) + 1)
        = ∑ i ∈ S, (b i : ℝ) * F (w i) + ∑ i ∈ S, (b i : ℝ) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [← hw₁] at hF2'
    linarith

  have hex : ∑ i ∈ S, (b i : ℝ) * F (w i)
      = ∑ j ∈ Finset.Icc 1 J, c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re) := by
    simp only [hF, Finset.mul_sum, Complex.re_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have e1 : (w i ^ j).re = R⁻¹ ^ j * (z i ^ j).re := by
      show ((((R⁻¹ : ℝ) : ℂ) * z i) ^ j).re = _
      rw [mul_pow, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    have e2 : ((b i : ℂ) * z i ^ j).re = (b i : ℝ) * (z i ^ j).re := by
      rw [← Complex.ofReal_natCast, Complex.re_ofReal_mul]
    rw [e1, e2]; ring

  have hup : ∀ j ∈ Finset.Icc 1 J,
      c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ 4 * J * δ * (1 + x) ^ J + 2 * L * (3 / 4 : ℝ) ^ j := by
    intro j hj
    obtain ⟨hj1, hjJ⟩ := Finset.mem_Icc.1 hj
    have hjJ' : (j : ℝ) ≤ J := by exact_mod_cast hjJ
    have hJ1 : (0 : ℝ) < J + 1 := by positivity
    have ha0 : 0 ≤ 1 - (j : ℝ) / (J + 1) := by
      rw [sub_nonneg, div_le_one hJ1]; linarith
    have ha1 : 1 - (j : ℝ) / (J + 1) ≤ 1 := by
      have : 0 ≤ (j : ℝ) / (J + 1) := by positivity
      linarith
    have hcos1 := Real.cos_le_one (j * θ)
    have hcos2 := Real.neg_one_le_cos (j * θ)
    have hc0 : 0 ≤ c j := mul_nonneg ha0 (by linarith)
    have hc2 : c j ≤ 2 := by
      show (1 - (j : ℝ) / (J + 1)) * (1 + Real.cos (j * θ)) ≤ 2
      nlinarith
    have hq : R⁻¹ ^ j ≤ (1 + x) ^ j := pow_le_pow_left₀ hRinv0 hRinv j
    have hq2 : (1 + x) ^ j ≤ (1 + x) ^ J := pow_le_pow_right₀ (by linarith) hjJ
    have hq3 : (1 + x) ^ j ≤ (3 / 2 : ℝ) ^ j := pow_le_pow_left₀ h1x.le (by linarith) j
    have hB0 : 0 ≤ 2 * j * δ + L / 2 ^ j := by positivity
    have s1 : R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re
        ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) :=
      (mul_le_mul_of_nonneg_left (hp j hj1) (by positivity)).trans
        (mul_le_mul_of_nonneg_right hq hB0)
    have s2 : (1 + x) ^ j * (2 * j * δ) ≤ (1 + x) ^ J * (2 * J * δ) := by gcongr
    have s3 : (1 + x) ^ j * (L / 2 ^ j) ≤ (3 / 2 : ℝ) ^ j * (L / 2 ^ j) := by gcongr
    have s4 : (3 / 2 : ℝ) ^ j * (L / 2 ^ j) = L * (3 / 4 : ℝ) ^ j := by
      have : (3 / 4 : ℝ) ^ j = (3 / 2 : ℝ) ^ j / 2 ^ j := by rw [← div_pow]; norm_num
      rw [this]; ring
    have s5 : 0 ≤ (1 + x) ^ j * (2 * j * δ + L / 2 ^ j) := by positivity
    calc c j * (R⁻¹ ^ j * (∑ i ∈ S, (b i : ℂ) * z i ^ j).re)
        ≤ c j * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_left s1 hc0
      _ ≤ 2 * ((1 + x) ^ j * (2 * j * δ + L / 2 ^ j)) := mul_le_mul_of_nonneg_right hc2 s5
      _ ≤ _ := by rw [mul_add ((1 + x) ^ j)]; linarith
  have hsum := Finset.sum_le_sum hup
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, Nat.card_Icc,
    Nat.add_sub_cancel, nsmul_eq_mul] at hsum
  have hg := sum_Icc_three_quarters_pow_le J
  have hg0 : (0 : ℝ) ≤ (3 / 4 : ℝ) ^ J := by positivity
  have hg' : 2 * L * ∑ j ∈ Finset.Icc 1 J, (3 / 4 : ℝ) ^ j ≤ 2 * L * 3 :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  have : (J : ℝ) * (4 * J * δ * (1 + x) ^ J) = 4 * (J : ℝ) ^ 2 * δ * (1 + x) ^ J := by ring
  linarith
end GlobalTheory
