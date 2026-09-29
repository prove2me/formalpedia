-- Prove2me | solution 1 for MeasureTheory.sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/eda462a2-3476-5158-a707-2eb80ec72180

import Mathlib
import Theorems.Thm_MeasureTheory_hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow
import Theorems.Thm_Complex_eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq

set_option autoImplicit false

open MeasureTheory

namespace LaurentCoeffFE

noncomputable def lcoeff (P : Polynomial ℂ) (n : ℤ) (j : ℤ) : ℂ :=
  if n ≤ j then P.coeff (j - n).toNat else 0

theorem lcoeff_natCast_add (P : Polynomial ℂ) (n : ℤ) (i : ℕ) :
    lcoeff P n ((i : ℤ) + n) = P.coeff i := by
  simp only [lcoeff]
  rw [if_pos (by omega)]
  congr 1
  omega

theorem lcoeff_eq_zero_of_not_mem (P : Polynomial ℂ) (n : ℤ) (j : ℤ)
    (hj : j ∉ Finset.image (fun i : ℕ => (i : ℤ) + n) (Finset.range (P.natDegree + 1))) :
    lcoeff P n j = 0 := by
  simp only [lcoeff]
  split_ifs with h
  · apply Polynomial.coeff_eq_zero_of_natDegree_lt
    by_contra hlt
    push Not at hlt
    apply hj
    refine Finset.mem_image.mpr ⟨(j - n).toNat, Finset.mem_range.mpr (by omega), ?_⟩
    rw [Int.toNat_of_nonneg (by omega)]
    ring
  · rfl

theorem hasSum_lcoeff (P : Polynomial ℂ) (n : ℤ) {Y : ℂ} (hY : Y ≠ 0) :
    HasSum (fun j : ℤ => lcoeff P n j * Y ^ j) (P.eval Y * Y ^ n) := by
  classical
  set s : Finset ℤ := Finset.image (fun i : ℕ => (i : ℤ) + n) (Finset.range (P.natDegree + 1)) with hs
  have hzero : ∀ j ∉ s, lcoeff P n j * Y ^ j = 0 := fun j hj => by
    rw [lcoeff_eq_zero_of_not_mem P n j hj, zero_mul]
  have h : HasSum (fun j : ℤ => lcoeff P n j * Y ^ j) (∑ j ∈ s, lcoeff P n j * Y ^ j) :=
    hasSum_sum_of_ne_finset_zero hzero
  convert h using 1
  rw [hs, Finset.sum_image (fun i _ i' _ h => by simpa using h)]
  rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lcoeff_natCast_add, zpow_add₀ hY, zpow_natCast]
  ring

theorem summable_norm_lcoeff (P : Polynomial ℂ) (n : ℤ) (r : ℝ) :
    Summable fun j : ℤ => ‖lcoeff P n j‖ * r ^ j := by
  refine summable_of_ne_finset_zero
    (s := Finset.image (fun i : ℕ => (i : ℤ) + n) (Finset.range (P.natDegree + 1))) fun j hj => ?_
  rw [lcoeff_eq_zero_of_not_mem P n j hj, norm_zero, zero_mul]

theorem hasSum_conv (c : ℤ → ℂ) (Q : Polynomial ℂ) {Y : ℂ} (hY : Y ≠ 0) {I : ℂ}
    (hc : HasSum (fun ℓ : ℤ => c ℓ * Y ^ ℓ) I) :
    HasSum (fun j : ℤ => (∑ i ∈ Q.support, Q.coeff i * c (j - (i : ℤ))) * Y ^ j)
      (I * Q.eval Y) := by
  have hterm : ∀ i ∈ Q.support,
      HasSum (fun j : ℤ => Q.coeff i * c (j - (i : ℤ)) * Y ^ j) (I * (Q.coeff i * Y ^ i)) := by
    intro i _

    have h1 : HasSum (fun ℓ : ℤ => c ℓ * Y ^ ℓ * (Q.coeff i * Y ^ i)) (I * (Q.coeff i * Y ^ i)) :=
      hc.mul_right _
    have h2 : (fun j : ℤ => Q.coeff i * c (j - (i : ℤ)) * Y ^ j) ∘ (Equiv.addRight (i : ℤ)) =
        fun ℓ : ℤ => c ℓ * Y ^ ℓ * (Q.coeff i * Y ^ i) := by
      funext ℓ
      simp only [Function.comp_apply, Equiv.coe_addRight, add_sub_cancel_right]
      rw [zpow_add₀ hY, zpow_natCast]
      ring
    exact (Equiv.hasSum_iff (Equiv.addRight (i : ℤ))).mp (h2 ▸ h1)
  have h := hasSum_sum hterm
  have hval : ∑ i ∈ Q.support, I * (Q.coeff i * Y ^ i) = I * Q.eval Y := by
    rw [← Finset.mul_sum, Polynomial.eval_eq_sum, Polynomial.sum_def]
  rw [hval] at h
  refine h.congr_fun fun j => ?_
  rw [Finset.sum_mul]

theorem summable_norm_conv (c : ℤ → ℂ) (Q : Polynomial ℂ) {r : ℝ} (hr : 0 < r)
    (hc : Summable fun ℓ : ℤ => ‖c ℓ‖ * r ^ ℓ) :
    Summable fun j : ℤ => ‖∑ i ∈ Q.support, Q.coeff i * c (j - (i : ℤ))‖ * r ^ j := by
  have hterm : ∀ i ∈ Q.support,
      Summable fun j : ℤ => ‖Q.coeff i‖ * r ^ (i : ℤ) * (‖c (j - (i : ℤ))‖ * r ^ (j - (i : ℤ))) := by
    intro i _
    have h1 : Summable ((fun ℓ : ℤ => ‖c ℓ‖ * r ^ ℓ) ∘ (Equiv.subRight (i : ℤ))) :=
      (Equiv.summable_iff (Equiv.subRight (i : ℤ))).mpr hc
    exact (h1.mul_left (‖Q.coeff i‖ * r ^ (i : ℤ))).congr fun j => by
      simp only [Function.comp_apply, Equiv.subRight_apply]
  have hsum := summable_sum hterm
  refine Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le j))
    (fun j => ?_) hsum
  calc ‖∑ i ∈ Q.support, Q.coeff i * c (j - (i : ℤ))‖ * r ^ j
      ≤ (∑ i ∈ Q.support, ‖Q.coeff i * c (j - (i : ℤ))‖) * r ^ j :=
        mul_le_mul_of_nonneg_right (norm_sum_le _ _) (zpow_nonneg hr.le j)
    _ = ∑ i ∈ Q.support, ‖Q.coeff i‖ * r ^ (i : ℤ) * (‖c (j - (i : ℤ))‖ * r ^ (j - (i : ℤ))) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, zpow_sub₀ hr.ne']
        field_simp

end LaurentCoeffFE

open LaurentCoeffFE in

theorem solution
    {T : Type*} [MeasurableSpace T] (μ : Measure T) (d : T → ℤ) (hd : Measurable d)
    (g : T → ℂ) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b)
    (hg : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b → Integrable (fun t => g t * Y ^ d t) μ)
    (Q P : Polynomial ℂ) (n : ℤ)
    (hfe : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b →
      (∫ t, g t * Y ^ d t ∂μ) * Q.eval Y = P.eval Y * Y ^ n)
    (j : ℤ) :
    ∑ i ∈ Q.support, Q.coeff i * ∫ t in d ⁻¹' {j - (i : ℤ)}, g t ∂μ =
      if n ≤ j then P.coeff (j - n).toNat else 0 := by

  set c : ℤ → ℂ := fun ℓ => ∫ t in d ⁻¹' {ℓ}, g t ∂μ with hc

  have hnorm : ∀ r : ℝ, a < r → r < b → ‖((r : ℝ) : ℂ)‖ = r := fun r har _ => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (ha.trans_lt har)]
  have hS : ∀ r : ℝ, a < r → r < b →
      (Summable fun ℓ : ℤ => ‖c ℓ‖ * r ^ ℓ) ∧
      ∀ Y : ℂ, ‖Y‖ = r → HasSum (fun ℓ : ℤ => c ℓ * Y ^ ℓ) (∫ t, g t * Y ^ d t ∂μ) := by
    intro r har hrb
    have hr : 0 < r := ha.trans_lt har
    have hint : Integrable (fun t => g t * (r : ℂ) ^ d t) μ :=
      hg (r : ℂ) (by rw [hnorm r har hrb]; exact har) (by rw [hnorm r har hrb]; exact hrb)
    obtain ⟨-, h2, h3⟩ := MeasureTheory.hasSum_setIntegral_preimage_mul_zpow_of_integrable_mul_zpow μ d hd g hr hint
    exact ⟨h2, fun Y hY => (h3 Y hY).2⟩

  set e : ℤ → ℂ := fun j => (∑ i ∈ Q.support, Q.coeff i * c (j - (i : ℤ))) - lcoeff P n j with he
  have hzero : ∀ Y : ℂ, a < ‖Y‖ → ‖Y‖ < b → ∑' j : ℤ, e j * Y ^ j = 0 := by
    intro Y haY hYb
    have hY : Y ≠ 0 := by
      intro h; rw [h, norm_zero] at haY; exact absurd haY (not_lt.mpr ha)
    have h1 := hasSum_conv c Q hY ((hS ‖Y‖ haY hYb).2 Y rfl)
    have h2 := hasSum_lcoeff P n hY
    have h3 := h1.sub h2
    rw [hfe Y haY hYb, sub_self] at h3
    have h4 : HasSum (fun j : ℤ => e j * Y ^ j) 0 := by
      refine h3.congr_fun fun j => ?_
      simp only [he]
      ring
    exact h4.tsum_eq
  have hsumm : ∀ r : ℝ, a < r → r < b → Summable fun j : ℤ => ‖e j‖ * r ^ j := by
    intro r har hrb
    have hr : 0 < r := ha.trans_lt har
    have h1 := summable_norm_conv c Q hr (hS r har hrb).1
    have h2 := summable_norm_lcoeff P n r
    refine Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (zpow_nonneg hr.le j))
      (fun j => ?_) (h1.add h2)
    calc ‖e j‖ * r ^ j ≤ (‖∑ i ∈ Q.support, Q.coeff i * c (j - (i : ℤ))‖ + ‖lcoeff P n j‖) * r ^ j :=
          mul_le_mul_of_nonneg_right (norm_sub_le _ _) (zpow_nonneg hr.le j)
      _ = _ := by ring

  set r₁ : ℝ := a + (b - a) / 3 with hr₁
  set r₂ : ℝ := a + 2 * ((b - a) / 3) with hr₂
  have har₁ : a < r₁ := by rw [hr₁]; linarith
  have hr₁₂ : r₁ < r₂ := by rw [hr₁, hr₂]; linarith
  have hr₂b : r₂ < b := by rw [hr₂]; linarith
  have h0 : 0 < r₁ := ha.trans_lt har₁
  have hU := Complex.eq_zero_of_summable_norm_mul_zpow_of_forall_tsum_mul_zpow_eq_zero e h0 hr₁₂
    (hsumm r₁ har₁ (hr₁₂.trans hr₂b)) (hsumm r₂ (har₁.trans hr₁₂) hr₂b)
    (fun z h1 h2 => hzero z (har₁.trans h1) (h2.trans hr₂b))
  have hj := congr_fun hU j
  simp only [he, Pi.zero_apply, sub_eq_zero] at hj
  simpa only [lcoeff] using hj

end S_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq
end P2MW
export P2MW.S_MeasureTheory_sum_coeff_mul_setIntegral_preimage_eq_of_forall_integral_mul_zpow_mul_eval_eq (solution)
