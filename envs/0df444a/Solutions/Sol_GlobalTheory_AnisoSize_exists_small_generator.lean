-- Prove2me | solution 1 for GlobalTheory.AnisoSize.exists_small_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:04:58.698742+00:00
-- url     : https://prove2.me/submissions/55a04f75-5a2e-45d3-a8ee-39f8006ff8b6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_IsLieDataCircle
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsNeZeroMemFractionalIdealNormSqLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_AnisotropicFiniteLengthsOfShortLatticeVector
import Theorems.Thm_GlobalTheory_AnisoSize_house_le
import Theorems.Thm_GlobalTheory_AnisoSize_absNorm_le
import Theorems.Thm_GlobalTheory_exists_ne_zero_mem_fractionalIdeal_norm_sq_le


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SmoothForms NumberField Matrix Module Submodule
open scoped ContDiff Topology nonZeroDivisors
open GlobalTheory GlobalTheory.AnisoSize
variable {E : Type} [Field E] [NumberField E]
variable (E)
namespace GlobalTheory.AnisoSize
theorem _root_.solution [IsTotallyComplex E] :
    ∃ (M : ℤ) (C : ℝ), M ≠ 0 ∧ ∀ J : Ideal (𝓞 E), J ≠ ⊥ →
      ∃ j ∈ J, j ≠ 0 ∧ house (algebraMap (𝓞 E) E j) ≤ C * Ideal.absNorm J ∧
        ∀ a ∈ J, j ∣ (M : 𝓞 E) * a := by
  set D : ℝ := √|(discr E : ℝ)| with hD
  have hD1 : 1 ≤ D := by
    rw [hD, Real.one_le_sqrt]
    exact_mod_cast Int.one_le_abs (discr_ne_zero E)
  refine ⟨(⌈D⌉₊).factorial, D, by exact_mod_cast Nat.factorial_ne_zero _, fun J hJ => ?_⟩
  have hf := IsTotallyComplex.finrank E
  set f := InfinitePlace.nrComplexPlaces E
  have hf0 : f ≠ 0 := by
    have : 0 < finrank ℚ E := finrank_pos
    omega
  obtain ⟨a, ha, ha0, hle⟩ := exists_ne_zero_mem_fractionalIdeal_norm_sq_le hf
    (J : FractionalIdeal (𝓞 E)⁰ E) (by simpa using hJ)
  obtain ⟨j, hj, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 ha
  rw [FractionalIdeal.coeIdeal_absNorm, ← hD] at hle
  have hN : Ideal.absNorm J ≠ 0 := by rwa [Ne, Ideal.absNorm_eq_zero_iff]
  have hN1 : (1 : ℝ) ≤ Ideal.absNorm J := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hN
  set X : ℝ := Ideal.absNorm J * D with hX
  have hX1 : 1 ≤ X := one_le_mul_of_one_le_of_one_le hN1 hD1
  have h1 : house (algebraMap (𝓞 E) E j) ^ finrank ℚ E ≤ X := by
    have h2 : house (algebraMap (𝓞 E) E j) ≤ √(X ^ ((f : ℝ)⁻¹)) := by
      refine house_le (Real.sqrt_nonneg _) fun φ => Real.le_sqrt_of_sq_le ((hle φ).trans ?_)
      have : 2 / Real.pi ≤ 1 := by
        rw [div_le_one Real.pi_pos]; exact Real.two_le_pi
      simpa [hX] using mul_le_of_le_one_left (b := X ^ ((f : ℝ)⁻¹)) (by positivity) this
    refine (pow_le_pow_left₀ (house_nonneg _) h2 _).trans (le_of_eq ?_)
    rw [hf, pow_mul, Real.sq_sqrt (by positivity), Real.rpow_inv_natCast_pow (by positivity) hf0]
  have hj0 : j ≠ 0 := by rintro rfl; simp at ha0
  refine ⟨j, hj, hj0, ?_, fun a ha => ?_⟩
  · rw [mul_comm]
    by_contra hc
    push Not at hc
    have := le_self_pow₀ (hX1.trans hc.le) (finrank_pos (R := ℚ) (M := E)).ne'
    linarith
  · obtain ⟨I, hI⟩ : J ∣ Ideal.span {j} := Ideal.dvd_span_singleton.2 hj
    have h3 := (absNorm_le j).trans h1
    rw [hI, map_mul, Nat.cast_mul, hX] at h3
    have h4 : (Ideal.absNorm I : ℝ) ≤ D := le_of_mul_le_mul_left h3 (by positivity)
    have h5 : Ideal.absNorm I ≤ ⌈D⌉₊ := by exact_mod_cast h4.trans (Nat.le_ceil D)
    have h6 : Ideal.absNorm I ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      rintro rfl
      exact hj0 (by simpa using hI)
    obtain ⟨m, hm⟩ := Nat.dvd_factorial (Nat.pos_of_ne_zero h6) h5
    rw [← Ideal.mem_span_singleton, hI, mul_comm J]
    refine Ideal.mul_mem_mul ?_ ha
    rw [hm]; push_cast
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem _)
end GlobalTheory.AnisoSize
