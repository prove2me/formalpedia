-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.r_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T17:35:03.77275+00:00
-- url     : https://prove2.me/submissions/3a1c400c-4cf5-4c7b-8db3-3a5abd168000

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
import Theorems.Thm_GlobalTheory_Hk_RaySq_mem_dv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
namespace GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
private lemma dvd_of_dvd_prime_pow_mul' {P C J : Ideal (𝓞 K)} (hP : Prime P) (hJ : ¬ P ∣ J) :
    ∀ k : ℕ, J ∣ P ^ k * C → J ∣ C := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    intro h
    apply ih
    obtain ⟨Y, hY⟩ := h
    have hPY : P ∣ J * Y := ⟨P ^ k * C, by rw [← hY]; ring⟩
    rcases hP.dvd_or_dvd hPY with h1 | ⟨Y', rfl⟩
    · exact absurd h1 hJ
    · refine ⟨Y', ?_⟩
      apply mul_left_cancel₀ hP.ne_zero
      calc P * (P ^ k * C) = P ^ (k + 1) * C := by ring
        _ = J * (P * Y') := hY
        _ = P * (J * Y') := by ring
variable {M : ℕ} (D : RayData K M)
end GlobalTheory.Hk.RaySq
end
end

set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution (f : Ideal (𝓞 K) → ℝ) (hf : ∀ I J, f (I * J) = f I * f J) {P C : Ideal (𝓞 K)} (hP : Prime P) (hC : C ≠ 0)
    (hPC : ¬ P ∣ C) (k : ℕ) : r f (P ^ (k + 1) * C) = f P * r f (P ^ k * C) + r f C := by
  have hP0 : P ≠ 0 := hP.ne_zero
  have hA : P ^ (k + 1) * C ≠ 0 := mul_ne_zero (pow_ne_zero _ hP0) hC
  have hB : P ^ k * C ≠ 0 := mul_ne_zero (pow_ne_zero _ hP0) hC
  have hsplit : dv (P ^ (k + 1) * C) = dv C ∪ (dv (P ^ k * C)).image (P * ·) := by
    ext J
    rw [Finset.mem_union, Finset.mem_image, mem_dv hA, mem_dv hC]
    constructor
    · intro h
      by_cases hJ : P ∣ J
      · right
        obtain ⟨J', rfl⟩ := hJ
        refine ⟨J', (mem_dv hB).2 ?_, rfl⟩
        obtain ⟨Y, hY⟩ := h
        refine ⟨Y, mul_left_cancel₀ hP0 ?_⟩
        calc P * (P ^ k * C) = P ^ (k + 1) * C := by ring
          _ = P * J' * Y := hY
          _ = P * (J' * Y) := by ring
      · left
        exact dvd_of_dvd_prime_pow_mul' hP hJ (k + 1) h
    · rintro (h | ⟨J', hJ', rfl⟩)
      · exact h.trans ⟨P ^ (k + 1), by ring⟩
      · rw [mem_dv hB] at hJ'
        have e : P * (P ^ k * C) = P ^ (k + 1) * C := by ring
        rw [← e]
        exact mul_dvd_mul_left P hJ'
  have hdisj : Disjoint (dv C) ((dv (P ^ k * C)).image (P * ·)) := by
    rw [Finset.disjoint_left]
    intro J hJ hJ'
    rw [mem_dv hC] at hJ
    obtain ⟨J', -, rfl⟩ := Finset.mem_image.1 hJ'
    exact hPC ((dvd_mul_right P J').trans hJ)
  unfold r
  rw [hsplit, Finset.sum_union hdisj, Finset.sum_image (fun a _ b _ hab => mul_left_cancel₀ hP0 hab)]
  simp only [hf, ← Finset.mul_sum]
  ring
end GlobalTheory.Hk.RaySq
