-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.r_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T18:07:03.426273+00:00
-- url     : https://prove2.me/submissions/439871b5-5ce9-4c46-b1b9-6c1055a96872

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
import Theorems.Thm_GlobalTheory_Hk_RaySq_r_pow
import Theorems.Thm_GlobalTheory_Hk_RaySq_geom_bounds
import Theorems.Thm_GlobalTheory_Hk_RaySq_r_one

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
theorem _root_.solution (f : Ideal (𝓞 K) → ℝ) (h1 : f 1 = 1) (hf : ∀ I J, f (I * J) = f I * f J)
    (hv : ∀ I, f I = 0 ∨ f I = 1 ∨ f I = -1) (C : Ideal (𝓞 K)) (hC : C ≠ 0) : 0 ≤ r f C ∧ 1 ≤ r f (C ^ 2) := by
  suffices h : ∀ N : ℕ, ∀ C : Ideal (𝓞 K), C ≠ 0 → Ideal.absNorm C = N →
      0 ≤ r f C ∧ 1 ≤ r f (C ^ 2) from h _ C hC rfl
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro C hC hN
  by_cases hu : IsUnit C
  · obtain rfl : C = 1 := isUnit_iff_eq_one.1 hu
    rw [one_pow, r_one f h1]
    norm_num
  · obtain ⟨P, hPirr, hPC⟩ := WfDvdMonoid.exists_irreducible_factor hu hC
    have hP : Prime P := UniqueFactorizationMonoid.irreducible_iff_prime.1 hPirr
    obtain ⟨k, D, hPD, rfl⟩ := WfDvdMonoid.max_power_factor hC hPirr
    have hD : D ≠ 0 := by
      rintro rfl
      exact hC (mul_zero _)
    have hk : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, one_mul] at hPC
      exact hPD hPC
    have hN2 : 2 ≤ Ideal.absNorm P := by
      have h0 : Ideal.absNorm P ≠ 0 := by
        rw [Ne, Ideal.absNorm_eq_zero_iff]
        exact hP.ne_zero
      have h1' : Ideal.absNorm P ≠ 1 := by
        rw [Ne, Ideal.absNorm_eq_one_iff]
        intro h
        apply hPirr.not_isUnit
        rw [h, ← Ideal.one_eq_top]
        exact isUnit_one
      omega
    have hD0 : 0 < Ideal.absNorm D := by
      apply Nat.pos_of_ne_zero
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact hD
    have hlt : Ideal.absNorm D < N := by
      rw [← hN, map_mul, map_pow]
      have h2 : 2 ≤ Ideal.absNorm P ^ k := le_trans hN2 (Nat.le_self_pow hk _)
      nlinarith
    obtain ⟨ihD1, ihD2⟩ := ih _ hlt D hD rfl
    have hPD2 : ¬ P ∣ D ^ 2 := by
      rw [pow_two]
      intro h
      rcases hP.dvd_or_dvd h with h | h <;> exact hPD h
    have hD2 : D ^ 2 ≠ 0 := pow_ne_zero _ hD
    obtain ⟨g1, g2⟩ := geom_bounds (hv P) k
    constructor
    · rw [r_pow f hf hP hD hPD k]
      exact mul_nonneg g1 ihD1
    · have e : (P ^ k * D) ^ 2 = P ^ (2 * k) * D ^ 2 := by ring
      rw [e, r_pow f hf hP hD2 hPD2 (2 * k)]
      exact one_le_mul_of_one_le_of_one_le g2 ihD2
end GlobalTheory.Hk.RaySq
