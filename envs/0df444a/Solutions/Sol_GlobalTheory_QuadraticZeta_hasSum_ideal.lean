-- Prove2me | solution 1 for GlobalTheory.QuadraticZeta.hasSum_ideal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:12:17.307395+00:00
-- url     : https://prove2.me/submissions/3c8bd3cf-75db-483a-babe-b5de1a82b493

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsIsKroneckerCharOfDiscr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsVariableChangeEqLatticeCurve
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsBasisEmbedding
import Theorems.Thm_GlobalTheory_QuadraticZeta_norm_eq_sq
import Theorems.Thm_GlobalTheory_QuadraticZeta_unit_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module FractionalIdeal
open scoped nonZeroDivisors UpperHalfPlane ComplexConjugate
open GlobalTheory GlobalTheory.QuadraticZeta
variable {K : Type*} [Field K] [NumberField K] {d : ℕ}
variable (h2 : finrank ℚ K = 2) (hD : discr K = -d) (σ : K →+* ℂ)
include h2 hD
namespace GlobalTheory.QuadraticZeta
theorem _root_.solution (hd : 4 < d) (𝔞 : (FractionalIdeal (𝓞 K)⁰ K)ˣ) {s S : ℝ} (hs : s ≠ 0)
    (h : HasSum (fun x : ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) =>
      (‖σ x‖ ^ 2 / absNorm 𝔞.1) ^ (-s)) S) :
    HasSum (fun I : Ideal (𝓞 K) => open Classical in
      if ((I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K).IsPrincipal
      then 2 * (Ideal.absNorm I : ℝ) ^ (-s) else 0) S := by
  have hΦ : ∀ x : ((𝔞 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ∃ I : Ideal (𝓞 K), (I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) = spanSingleton _ (x : K) := by
    intro x
    obtain ⟨I, hI⟩ := le_one_iff_exists_coeIdeal.1
      (show spanSingleton (𝓞 K)⁰ (x : K) * (𝔞⁻¹).1 ≤ 1 by
        rw [← 𝔞.mul_inv]
        gcongr
        exact spanSingleton_le_iff_mem.2 x.2)
    exact ⟨I, by rw [hI, mul_assoc, 𝔞.inv_mul, mul_one]⟩
  choose Φ hΦ using hΦ
  have hmem : ∀ x I, x ∈ Φ ⁻¹' {I} ↔
      (I * 𝔞 : FractionalIdeal (𝓞 K)⁰ K) = spanSingleton _ (x : K) := fun x I => by
    rw [← hΦ, Units.mul_left_inj, coeIdeal_inj, Set.mem_preimage, Set.mem_singleton_iff, eq_comm]
  have hN : (absNorm 𝔞.1 : ℝ) ≠ 0 := by simp [absNorm_eq_zero_iff]
  refine (h.tsum_fiberwise Φ).congr_fun fun I => ?_
  have hval : ∀ x : Φ ⁻¹' {I}, (‖σ x.1‖ ^ 2 / absNorm 𝔞.1) ^ (-s)
      = (Ideal.absNorm I : ℝ) ^ (-s) := fun x => by
    have := congrArg (fun J => ((absNorm J : ℚ) : ℝ)) ((hmem _ _).1 x.2)
    simp only [map_mul, coeIdeal_absNorm, absNorm_span_singleton, Rat.cast_mul, Rat.cast_abs,
      Rat.cast_natCast, norm_eq_sq h2 hD σ, abs_pow, abs_norm] at this
    rw [← this, mul_div_cancel_right₀ _ hN]
  rw [tsum_congr hval, tsum_const, nsmul_eq_mul]
  rcases eq_or_ne I ⊥ with rfl | hI
  · simp [Real.zero_rpow (neg_ne_zero.2 hs)]
  split_ifs with hP
  · obtain ⟨x, hx⟩ := (isPrincipal_iff _).1 hP
    have hx0 : x ≠ 0 := by
      rintro rfl
      simp [hI] at hx
    have hxa : x ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
      rw [← spanSingleton_le_iff_mem, ← hx]
      exact (mul_le_mul_left coeIdeal_le_one _).trans (one_mul _).le
    have : Φ ⁻¹' {I} = {⟨x, hxa⟩, -⟨x, hxa⟩} := by
      ext y
      rw [hmem, hx, spanSingleton_eq_spanSingleton]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Subtype.ext_iff, Submodule.coe_neg]
      constructor
      · rintro ⟨u, hu⟩
        rcases unit_eq h2 hD σ hd u with rfl | rfl
        · exact Or.inl (by simpa using hu.symm)
        · exact Or.inr (by simpa using hu.symm)
      · rintro (h | h)
        · exact ⟨1, by simp [h]⟩
        · exact ⟨-1, by simp [h]⟩
    rw [this, Nat.card_coe_set_eq, Set.ncard_pair]
    · simp
    · intro e
      exact hx0 (by simpa [Subtype.ext_iff, CharZero.eq_neg_self_iff] using e)
  · have : Φ ⁻¹' {I} = ∅ := Set.eq_empty_of_forall_notMem fun y hy =>
      hP ((isPrincipal_iff _).2 ⟨y, (hmem _ _).1 hy⟩)
    simp [this]
end GlobalTheory.QuadraticZeta
