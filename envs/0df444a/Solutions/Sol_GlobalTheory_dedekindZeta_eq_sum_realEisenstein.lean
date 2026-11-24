-- Prove2me | solution 1 for GlobalTheory.dedekindZeta_eq_sum_realEisenstein
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:37.658864+00:00
-- url     : https://prove2.me/submissions/923d8b1d-ec82-4249-99b1-a9a0ff6e8c4f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoRealEisensteinSubPole
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_DedekindZetaEqSumRealEisenstein
import Theorems.Thm_GlobalTheory_QuadraticZeta_hasSum_ideal_of_image
import Theorems.Thm_GlobalTheory_summable_realEisenstein


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal Filter Topology
open scoped nonZeroDivisors UpperHalfPlane Real
open GlobalTheory
open QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
namespace GlobalTheory
theorem _root_.solution (h2 : finrank ℚ K = 2) (hD : discr K = -d) (hd : 4 < d)
    (σ : K →+* ℂ) {τ : ClassGroup (𝓞 K) → ℍ} (hτ : ∀ c, IsIdealClassPoint σ c (τ c))
    {s : ℝ} (hs : 1 < s) :
    dedekindZeta K s = ((2 / √d) ^ s / 2 * ∑ c, ∑' p : {p : ℤ × ℤ // p ≠ 0},
      (τ c).im ^ s / ‖(p.1.1 * τ c + p.1.2 : ℂ)‖ ^ (2 * s) : ℝ) := by
  classical
  choose 𝔞 ω hc h using hτ
  have hs0 : -s ≠ 0 := by linarith
  have h1 := (hasSum_sum fun c (_ : c ∈ Finset.univ) => hasSum_ideal_of_image h2 hD σ hd (𝔞 c)
    (h c) hs (summable_realEisenstein _ hs)).div_const 2
  rw [← Finset.mul_sum, mul_div_right_comm] at h1
  have h3 : HasSum (fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-s)) _ :=
    h1.congr_fun fun I => by
      rcases eq_or_ne I ⊥ with rfl | hI
      · simp [Real.zero_rpow hs0]
      have hI' : I ∈ (Ideal (𝓞 K))⁰ := mem_nonZeroDivisors_of_ne_zero hI
      have : ∀ c, ((I * 𝔞 c : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal ↔
          (ClassGroup.mk0 ⟨I, hI'⟩)⁻¹ = c := fun c => by
        rw [inv_eq_iff_mul_eq_one, ← ClassGroup.mk_mk0 K]
        conv_rhs => rw [← hc c, ← map_mul, ClassGroup.mk_eq_one_iff]
        rfl
      simp only [this, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      ring
  have h4 := Complex.hasSum_ofReal.2 (h3.tsum_fiberwise Ideal.absNorm)
  rw [dedekindZeta, LSeries]
  refine HasSum.tsum_eq (h4.congr_fun fun n => ?_)
  rw [tsum_congr (g := fun _ => (n : ℝ) ^ (-s)) fun I => by
    rw [show Ideal.absNorm I.1 = n from I.2], tsum_const, nsmul_eq_mul]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [Real.zero_rpow hs0]
  · rw [LSeries.term_of_ne_zero hn, Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_neg, Complex.cpow_neg]
    rfl
end GlobalTheory
