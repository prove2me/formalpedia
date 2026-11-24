-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.conv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:10.10281+00:00
-- url     : https://prove2.me/submissions/a70f87e7-5614-4c43-93ba-7847904a229e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
import Theorems.Thm_GlobalTheory_Hk_RaySq_mem_normEq
import Theorems.Thm_GlobalTheory_Hk_RaySq_mem_dv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution (F : Ideal (𝓞 K) → Ideal (𝓞 K) → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J =
      ∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J := by
  have L : (∑ p ∈ n.divisorsAntidiagonal, ∑ I ∈ normEq K p.1, ∑ J ∈ normEq K p.2, F (I * J) J) =
      ∑ y ∈ n.divisorsAntidiagonal.sigma (fun p => normEq K p.1 ×ˢ normEq K p.2),
        F (y.2.1 * y.2.2) y.2.2 := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_product]
  have R : (∑ C ∈ normEq K n, ∑ J ∈ dv C, F C J) =
      ∑ y ∈ (normEq K n).sigma (fun C => dv C), F y.1 y.2 := by
    rw [Finset.sum_sigma]
  rw [L, R]
  refine Finset.sum_nbij'
    (fun y : (Σ _ : ℕ × ℕ, Ideal (𝓞 K) × Ideal (𝓞 K)) =>
      (⟨y.2.1 * y.2.2, y.2.2⟩ : Σ _ : Ideal (𝓞 K), Ideal (𝓞 K)))
    (fun y : (Σ _ : Ideal (𝓞 K), Ideal (𝓞 K)) =>
      (⟨(Ideal.absNorm y.1 / Ideal.absNorm y.2, Ideal.absNorm y.2),
        ((if h : y.2 ∣ y.1 then Exists.choose h else 0), y.2)⟩ :
        Σ _ : ℕ × ℕ, Ideal (𝓞 K) × Ideal (𝓞 K))) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨⟨a, b⟩, I, J⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy ⊢
    obtain ⟨⟨hab, -⟩, hI, hJ⟩ := hy
    have hIJ0 : I * J ≠ 0 := by
      intro h
      have e := congrArg Ideal.absNorm h
      rw [map_mul, _root_.map_zero, hI, hJ, hab] at e
      exact hn e
    exact ⟨by rw [map_mul, hI, hJ, hab], (mem_dv hIJ0).2 (dvd_mul_left J I)⟩
  · rintro ⟨C, J⟩ hy
    simp only [Finset.mem_sigma, mem_normEq] at hy
    obtain ⟨hCn, hJ⟩ := hy
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hCn
      exact hn hCn.symm
    obtain ⟨c, rfl⟩ := (mem_dv hC0).1 hJ
    have hJ0 : J ≠ 0 := by
      rintro rfl
      exact hC0 (zero_mul c)
    have hch : (if h : J ∣ J * c then Exists.choose h else 0) = c := by
      rw [dif_pos (dvd_mul_right J c)]
      exact mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm
    have hNJ : 0 < Ideal.absNorm J := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hJ0
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq]
    rw [hch, map_mul, Nat.mul_div_cancel_left _ hNJ]
    rw [map_mul] at hCn
    exact ⟨⟨by rw [mul_comm]; exact hCn, hn⟩, rfl, trivial⟩
  · rintro ⟨⟨a, b⟩, I, J⟩ hy
    simp only [Finset.mem_sigma, Finset.mem_product, Nat.mem_divisorsAntidiagonal, mem_normEq] at hy
    obtain ⟨⟨hab, -⟩, hI, hJ⟩ := hy
    have hJ0 : J ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hJ
      subst hJ
      exact hn (by rw [← hab, mul_zero])
    have hNJ : 0 < Ideal.absNorm J := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hJ0
    have hch : (if h : J ∣ I * J then Exists.choose h else 0) = I := by
      rw [dif_pos (dvd_mul_left J I)]
      apply mul_left_cancel₀ hJ0
      rw [← Exists.choose_spec (dvd_mul_left J I), mul_comm]
    dsimp only
    rw [hch, map_mul, Nat.mul_div_cancel _ hNJ, hI, hJ]
  · rintro ⟨C, J⟩ hy
    simp only [Finset.mem_sigma, mem_normEq] at hy
    obtain ⟨hCn, hJ⟩ := hy
    have hC0 : C ≠ 0 := by
      rintro rfl
      rw [_root_.map_zero] at hCn
      exact hn hCn.symm
    obtain ⟨c, rfl⟩ := (mem_dv hC0).1 hJ
    have hJ0 : J ≠ 0 := by
      rintro rfl
      exact hC0 (zero_mul c)
    have hch : (if h : J ∣ J * c then Exists.choose h else 0) = c := by
      rw [dif_pos (dvd_mul_right J c)]
      exact mul_left_cancel₀ hJ0 (Exists.choose_spec (dvd_mul_right J c)).symm
    dsimp only
    rw [hch, mul_comm]
  · rintro ⟨p, I, J⟩ _
    rfl
end GlobalTheory.Hk.RaySq
