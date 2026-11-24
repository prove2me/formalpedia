-- Prove2me | solution 1 for GlobalTheory.LOneLower.lambert_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:52:06.128138+00:00
-- url     : https://prove2.me/submissions/b72b8582-e11c-4145-828b-2a641613203d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ExistsLeNormLFunctionOne
import Theorems.Thm_GlobalTheory_LOneLower_one_le_zetaMul_sq
import Theorems.Thm_GlobalTheory_LOneLower_lambert

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open Filter Topology
open scoped ComplexOrder
open GlobalTheory GlobalTheory.LOneLower
namespace GlobalTheory.LOneLower
theorem _root_.solution {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {M : ℕ}
    (hM : 0 < M) :
    (M : ℝ) / 3 ≤ ‖∑' d : ℕ, χ ((d + 1 : ℕ) : ZMod q) *
      (((Real.exp (((d + 1 : ℕ) : ℝ) * ((M : ℝ) ^ 2)⁻¹) - 1)⁻¹ : ℝ) : ℂ)‖ := by
  set α : ℝ := ((M : ℝ) ^ 2)⁻¹ with hα
  have hα0 : 0 < α := by positivity
  set t : ℝ := Real.exp (-α) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have hn : ‖(t : ℂ)‖ < 1 := by rwa [Complex.norm_real, Real.norm_of_nonneg ht0.le]
  have h1 := lambert χ hn
  rw [tsum_pnat_eq_tsum_succ
    (f := fun d : ℕ => χ (d : ZMod q) * ((t : ℂ) ^ d / (1 - (t : ℂ) ^ d)))] at h1
  have e : ∀ d : ℕ, (((Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ : ℝ) : ℂ)
      = (t : ℂ) ^ (d + 1) / (1 - (t : ℂ) ^ (d + 1)) := by
    intro d
    have : t ^ (d + 1) = (Real.exp (((d + 1 : ℕ) : ℝ) * α))⁻¹ := by
      rw [ht, ← Real.exp_nat_mul, ← Real.exp_neg, mul_neg]
    have h2 : (Real.exp (((d + 1 : ℕ) : ℝ) * α) - 1)⁻¹ = t ^ (d + 1) / (1 - t ^ (d + 1)) := by
      rw [this]
      have h3 : 0 < ((d + 1 : ℕ) : ℝ) * α := by positivity
      have h4 := Real.add_one_le_exp (((d + 1 : ℕ) : ℝ) * α)
      generalize Real.exp (((d + 1 : ℕ) : ℝ) * α) = E at *
      have h5 : E - 1 ≠ 0 := by linarith
      have h6 : E ≠ 0 := by linarith
      field_simp
    rw [h2]
    push_cast
    rfl
  simp only [e]
  refine le_trans ?_ (Complex.re_le_norm _)
  have h3 := Complex.hasSum_re h1
  have hre : ∀ n : ℕ, (zetaMul χ n * (t : ℂ) ^ n).re = (zetaMul χ n).re * t ^ n := by
    intro n
    rw [← Complex.ofReal_pow, Complex.re_mul_ofReal]
  simp only [hre] at h3
  let g : ℕ → ℕ+ := fun m => m.succPNat ^ 2
  have hg : Function.Injective g := by
    intro a b hab
    have := congrArg PNat.val hab
    simp only [g, PNat.pow_coe, Nat.succPNat_coe] at this
    have := Nat.pow_left_injective two_ne_zero this
    omega
  refine le_trans ?_ (sum_le_hasSum ((Finset.range M).image g) (fun n _ => ?_) h3)
  · rw [Finset.sum_image fun a _ b _ h => hg h]
    have : ∀ m ∈ Finset.range M, (1 / 3 : ℝ) ≤ (zetaMul χ (g m)).re * t ^ (g m : ℕ) := by
      intro m hm
      have hgm : (g m : ℕ) = (m + 1) ^ 2 := by simp [g]
      rw [hgm]
      have h4 : 1 ≤ (zetaMul χ ((m + 1) ^ 2)).re :=
        (Complex.le_def.1 (one_le_zetaMul_sq hχ (Nat.succ_ne_zero m))).1
      have h5 : t ^ (M ^ 2) ≤ t ^ ((m + 1) ^ 2) :=
        pow_le_pow_of_le_one ht0.le ht1.le
          (Nat.pow_le_pow_left (Finset.mem_range.1 hm) 2)
      have h6 : t ^ (M ^ 2) = Real.exp (-1) := by
        rw [ht, ← Real.exp_nat_mul, hα]
        congr 1
        push_cast
        field_simp
      have h7 : (1 / 3 : ℝ) ≤ Real.exp (-1) := by linarith [Real.exp_neg_one_gt_d9]
      nlinarith
    have := Finset.card_nsmul_le_sum _ _ _ this
    simpa [div_eq_mul_inv] using this
  · exact mul_nonneg (Complex.le_def.1 (zetaMul_nonneg hχ n)).1 (pow_nonneg ht0.le _)
end GlobalTheory.LOneLower
