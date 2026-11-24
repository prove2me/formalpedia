-- Prove2me | solution 1 for MomentComparison.twoPoint_contract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:17:34.405142+00:00
-- url     : https://prove2.me/submissions/ea56247f-410a-4ea1-8cbf-4bef507e3d93

module
public import Definitions.Def_MomentComparison_TwoPoint
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Definitions.Def_MomentComparison_TwoPointReduction
public import Theorems.Thm_MomentComparison_anisotropic_sq_le
public import Theorems.Thm_MomentComparison_onePointLower
public import Theorems.Thm_MomentComparison_onePointUpper

section
public section
namespace MomentComparison
private lemma twoPointMoment_nonneg (s : ℝ) (a b : ℂ) : 0 ≤ twoPointMoment s a b := by
  unfold twoPointMoment
  positivity
private lemma twoPointMoment_zero_left (s : ℝ) (b : ℂ) :
    twoPointMoment s 0 b = ‖b‖ ^ s := by
  simp only [twoPointMoment, zero_add, zero_sub, norm_neg]
  ring
private lemma twoPointMoment_mul (s : ℝ) (a b c : ℂ) :
    twoPointMoment s (a * b) (a * c) = ‖a‖ ^ s * twoPointMoment s b c := by
  unfold twoPointMoment
  rw [← mul_add, ← mul_sub, norm_mul, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _),
    Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  ring
private lemma norm_le_one_of_inLens {p : ℝ} (hp : 2 < p) {w : ℂ} (hw : inLens p w) :
    ‖w‖ ≤ 1 := by
  have h := anisotropic_sq_le (z := 1) hp hw
  simp only [mul_one, Complex.one_re, Complex.one_im, one_pow,
    zero_pow (by decide : (2 : ℕ) ≠ 0), add_zero] at h
  have hnonneg : 0 ≤ (p - 2) * w.re ^ 2 := by positivity
  have ht : (p - 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hs := Complex.sq_norm w
  rw [Complex.normSq_apply] at hs
  nlinarith [norm_nonneg w]
private theorem twoPoint_contract_of_onePoint
    (hUpper : ∀ {p : ℝ}, 2 ≤ p → ∀ z : ℂ,
      ((‖1 + z‖ ^ p + ‖1 - z‖ ^ p) / 2) ^ (2 / p) ≤ 1 + (p - 1) * z.re ^ 2 + z.im ^ 2)
    (hLower : ∀ {p : ℝ}, 1 < p → p ≤ 2 → ∀ z : ℂ,
      1 + (p - 1) * z.re ^ 2 + z.im ^ 2 ≤ ((‖1 + z‖ ^ p + ‖1 - z‖ ^ p) / 2) ^ (2 / p))
    {p : ℝ} (hp : 2 < p) {w : ℂ} (hw : inLens p w) (a b : ℂ) :
    ((‖a + w * b‖ ^ p + ‖a - w * b‖ ^ p) / 2) ^ p⁻¹ ≤
      ((‖a + b‖ ^ (p / (p - 1)) + ‖a - b‖ ^ (p / (p - 1))) / 2) ^ (p / (p - 1))⁻¹ := by
  let q := p / (p - 1)
  change twoPointMoment p a (w * b) ^ p⁻¹ ≤ twoPointMoment q a b ^ q⁻¹
  have hden : 0 < p - 1 := by linarith
  have hq₁ : 1 < q := (lt_div_iff₀ hden).mpr (by linarith)
  have hq₂ : q ≤ 2 := (div_le_iff₀ hden).mpr (by linarith)
  have hp₀ : p ≠ 0 := by linarith
  have hq₀ : q ≠ 0 := by linarith
  by_cases ha : a = 0
  · subst a
    rw [twoPointMoment_zero_left, twoPointMoment_zero_left,
      Real.rpow_rpow_inv (norm_nonneg _) hp₀, Real.rpow_rpow_inv (norm_nonneg _) hq₀, norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg b) (norm_le_one_of_inLens hp hw)
  · let z := b / a
    have hab : a * z = b := by dsimp [z]; field_simp
    have habw : a * (w * z) = w * b := by rw [mul_left_comm, hab]
    have hq_eq : q - 1 = (p - 1)⁻¹ := by dsimp [q]; field_simp; ring
    have hn : twoPointMoment p 1 (w * z) ^ (2 / p) ≤
        twoPointMoment q 1 z ^ (2 / q) := by
      calc
        _ ≤ 1 + (p - 1) * (w * z).re ^ 2 + (w * z).im ^ 2 := hUpper hp.le _
        _ ≤ 1 + (q - 1) * z.re ^ 2 + z.im ^ 2 := by
          have h := anisotropic_sq_le (z := z) hp hw
          rw [hq_eq]
          linarith
        _ ≤ _ := hLower hq₁ hq₂ _
    have hhalf := Real.rpow_le_rpow (Real.rpow_nonneg (twoPointMoment_nonneg p 1 (w * z)) _) hn
      (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    rw [← Real.rpow_mul (twoPointMoment_nonneg p 1 (w * z)),
      ← Real.rpow_mul (twoPointMoment_nonneg q 1 z),
      show 2 / p * (1 / 2 : ℝ) = p⁻¹ by ring,
      show 2 / q * (1 / 2 : ℝ) = q⁻¹ by ring] at hhalf
    conv_lhs =>
      rw [← habw]
      conv in twoPointMoment p a _ => arg 2; rw [← mul_one a]
      rw [twoPointMoment_mul, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _)
        (twoPointMoment_nonneg _ _ _), Real.rpow_rpow_inv (norm_nonneg _) hp₀]
    conv_rhs =>
      rw [← hab]
      conv in twoPointMoment q a _ => arg 2; rw [← mul_one a]
      rw [twoPointMoment_mul, Real.mul_rpow (Real.rpow_nonneg (norm_nonneg _) _)
        (twoPointMoment_nonneg _ _ _), Real.rpow_rpow_inv (norm_nonneg _) hq₀]
    exact mul_le_mul_of_nonneg_left hhalf (norm_nonneg a)
end MomentComparison
end
end

set_option autoImplicit true
@[expose] public section
public section
open MomentComparison
namespace MomentComparison
theorem _root_.solution {p : ℝ} (hp : 2 < p) {w : ℂ} (hw : inLens p w) (a b : ℂ) :
    ((‖a + w * b‖ ^ p + ‖a - w * b‖ ^ p) / 2) ^ p⁻¹ ≤
      ((‖a + b‖ ^ (p / (p - 1)) + ‖a - b‖ ^ (p / (p - 1))) / 2) ^ (p / (p - 1))⁻¹ :=
  twoPoint_contract_of_onePoint onePointUpper onePointLower hp hw a b
end MomentComparison
