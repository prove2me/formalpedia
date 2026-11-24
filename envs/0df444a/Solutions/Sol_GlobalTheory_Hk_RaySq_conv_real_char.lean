-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.conv_real_char
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:25:42.307805+00:00
-- url     : https://prove2.me/submissions/7526c5b7-1973-4f45-bf90-9648e6a5ddce

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
import Theorems.Thm_GlobalTheory_Hk_RaySq_mem_normEq
import Theorems.Thm_GlobalTheory_Hk_RaySq_r_bounds
import Theorems.Thm_GlobalTheory_Hk_RaySq_sum_aRay
import Theorems.Thm_GlobalTheory_Hk_RaySq_chi_mul
import Theorems.Thm_GlobalTheory_Hk_RaySq_chi_one
import Theorems.Thm_GlobalTheory_Hk_RaySq_conv_aRay

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
variable {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (ε : D.G → ℝ), ε 1 = 1 → (∀ g h, ε (g * h) = ε g * ε h) → (∀ g, ε g = 1 ∨ ε g = -1) → ∀ n : ℕ, 0 ≤ ∑ p ∈ n.divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 ∧ ∑ g, aRay D g n ≤ ∑ p ∈ (n ^ 2).divisorsAntidiagonal, (∑ g, aRay D g p.1) * ∑ g, ε g * aRay D g p.2 := by
  intro K _ _ M _ D ε h1 hmul hpm n
  have hv : ∀ I, chi D ε I = 0 ∨ chi D ε I = 1 ∨ chi D ε I = -1 := by
    intro I
    unfold chi
    split_ifs
    · rcases hpm (D.cls I) with h | h <;> simp [h]
    · simp
  have hr : ∀ C : Ideal (𝓞 K), C ≠ 0 → 0 ≤ r (chi D ε) C ∧ 1 ≤ r (chi D ε) (C ^ 2) :=
    fun C hC => r_bounds (chi D ε) (chi_one D ε h1) (chi_mul D ε hmul) hv C hC
  have h01 : ∀ I, chi D (fun _ => 1) I =
      if I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)}) then 1 else 0 := fun I => rfl
  have hterm : ∀ C : Ideal (𝓞 K), 0 ≤ chi D (fun _ => 1) C * r (chi D ε) C := by
    intro C
    rw [h01]
    split_ifs with h
    · rw [one_mul]
      exact (hr C h.1).1
    · rw [zero_mul]
  have hsum1 : ∀ m, ∑ g, aRay D g m = ∑ I ∈ normEq K m, chi D (fun _ => 1) I := by
    intro m
    rw [← sum_aRay D (fun _ => 1) m]
    simp
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨by simp, ?_⟩
    have h0 : ∑ I ∈ normEq K 0, chi D (fun _ => 1) I = 0 := by
      refine Finset.sum_eq_zero fun I hI => ?_
      rw [mem_normEq, Ideal.absNorm_eq_zero_iff] at hI
      simp [chi, hI]
    rw [hsum1, h0]
    simp
  · have hn0 : n ≠ 0 := hn.ne'
    rw [conv_aRay D ε hn0, conv_aRay D ε (pow_ne_zero 2 hn0), hsum1]
    refine ⟨Finset.sum_nonneg fun C _ => hterm C, ?_⟩
    calc ∑ I ∈ normEq K n, chi D (fun _ => 1) I
        ≤ ∑ I ∈ normEq K n, chi D (fun _ => 1) (I ^ 2) * r (chi D ε) (I ^ 2) := by
          refine Finset.sum_le_sum fun I _ => ?_
          by_cases h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
          · have h2 : I ^ 2 ≠ ⊥ ∧ IsCoprime (I ^ 2) (Ideal.span {(M : 𝓞 K)}) :=
              ⟨pow_ne_zero 2 h.1, h.2.pow_left⟩
            rw [h01, h01, if_pos h, if_pos h2, one_mul]
            exact (hr I h.1).2
          · rw [h01 I, if_neg h]
            exact hterm (I ^ 2)
      _ = ∑ C ∈ (normEq K n).image (· ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by
          rw [Finset.sum_image]
          intro a _ b _ hab
          have hab' : a ^ 2 = b ^ 2 := hab
          exact dvd_antisymm ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.dvd)
            ((UniqueFactorizationMonoid.pow_dvd_pow_iff_dvd two_ne_zero).1 hab'.symm.dvd)
      _ ≤ ∑ C ∈ normEq K (n ^ 2), chi D (fun _ => 1) C * r (chi D ε) C := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun C _ _ => hterm C
          intro C hC
          obtain ⟨I, hI, rfl⟩ := Finset.mem_image.1 hC
          rw [mem_normEq] at hI ⊢
          rw [map_pow, hI]
end GlobalTheory.Hk.RaySq
