-- Prove2me | solution 1 for GlobalTheory.CompactQuotientFourier.inversion_at_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:45:13.093802+00:00
-- url     : https://prove2.me/submissions/558fba3f-f585-45b3-944f-fe86130aafaa

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_EqZeroOfCoefficientsSeparatingCharactersEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_FourierInversionZeroCompactQuotient
import Theorems.Thm_GlobalTheory_CompactQuotientFourier_setIntegral_translate
import Theorems.Thm_GlobalTheory_SeparatingCharacters_eq_zero_of_coefficients_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.CompactQuotientFourier
namespace GlobalTheory.CompactQuotientFourier
theorem _root_.solution : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] [Countable A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → (∀ a, (∀ x, χ a x = 1) → a = 0) → ∀ (μ : Measure G) (𝓕 : Set G), μ.IsAddHaarMeasure → IsAddFundamentalDomain Γ 𝓕 μ → μ 𝓕 = 1 → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → Summable (fun a => ‖∫ x in 𝓕, χ a x * Φ x ∂μ‖) → Φ 0 = ∑' a, ∫ x in 𝓕, χ a x * Φ x ∂μ := by
  intro G _ _ _ _ _ _ _ _ Γ _ K hK hcov A _ _ χ hc hx ha hn hker hinj μ 𝓕 hμ h𝓕 h1 Φ hΦ hper hsum
  classical
  haveI := hμ
  have : Countable Γ := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have : IsFiniteMeasure (μ.restrict 𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, h1]; exact ENNReal.one_lt_top⟩
  have hvol : μ.real 𝓕 = 1 := by simp [Measure.real, h1]
  have hne : ∀ a x, χ a x ≠ 0 := fun a x h => by simpa [h] using hn a x
  have hχ0 : ∀ x, χ 0 x = 1 := fun x => by
    have h2 : χ 0 x * χ 0 x = χ 0 x * 1 := by rw [mul_one, ← ha, add_zero]
    exact mul_left_cancel₀ (hne 0 x) h2
  have hχx0 : ∀ a, χ a 0 = 1 := fun a => by
    have h2 : χ a 0 * χ a 0 = χ a 0 * 1 := by rw [mul_one, ← hx, add_zero]
    exact mul_left_cancel₀ (hne a 0) h2
  have hstar : ∀ a x, star (χ a x) = χ (-a) x := fun a x => by
    have h1' : χ (-a) x * χ a x = 1 := by rw [← ha, neg_add_cancel, hχ0]
    have h2 : star (χ a x) * χ a x = 1 := by simp [Complex.conj_mul', hn]
    exact mul_right_cancel₀ (hne a x) (h2.trans h1'.symm)
  have hperχ : ∀ a, ∀ γ ∈ Γ, ∀ x, χ a (γ + x) = χ a x := fun a γ hγ x => by
    rw [hx, (hker γ).2 hγ a, one_mul]
  have horth : ∀ a b, ∫ x in 𝓕, χ b x * star (χ a x) ∂μ = if a = b then 1 else 0 := by
    intro a b
    have he : ∀ x, χ b x * star (χ a x) = χ (b - a) x := fun x => by rw [hstar, ← ha, sub_eq_add_neg]
    simp_rw [he]
    split_ifs with hab
    · subst hab
      simp [hχ0, hvol]
    · have hc' : b - a ≠ 0 := sub_ne_zero.2 (Ne.symm hab)
      obtain ⟨x₀, hx₀⟩ : ∃ x₀, χ (b - a) x₀ ≠ 1 := by
        by_contra h
        push_neg at h
        exact hc' (hinj _ h)
      have key := setIntegral_translate Γ μ 𝓕 h𝓕 (χ (b - a)) (hperχ _) x₀
      simp_rw [hx _ _ x₀] at key
      rw [integral_mul_const] at key
      have h3 : (∫ x in 𝓕, χ (b - a) x ∂μ) * (χ (b - a) x₀ - 1) = 0 := by
        rw [mul_sub, key, mul_one, sub_self]
      exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 hx₀)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hΦ.continuousOn
  have hΦb : ∀ x, ‖Φ x‖ ≤ C := fun x => by
    obtain ⟨γ, hγ, hk⟩ := hcov x
    rw [← hper γ hγ x]
    exact hC _ hk
  have hint : ∀ f : G → ℂ, Continuous f → ∀ B, (∀ x, ‖f x‖ ≤ B) → Integrable f (μ.restrict 𝓕) :=
    fun f hf B hB => Integrable.of_bound hf.aestronglyMeasurable B (Filter.Eventually.of_forall hB)
  set c : A → ℂ := fun a => ∫ x in 𝓕, χ a x * Φ x ∂μ with hcdef
  have hterm : ∀ a x, ‖c a * star (χ a x)‖ = ‖c a‖ := fun a x => by
    rw [norm_mul, norm_star, hn, mul_one]
  let S : G → ℂ := fun x => ∑' a, c a * star (χ a x)
  have hScont : Continuous S :=
    continuous_tsum (fun a => continuous_const.mul (hc a).star) hsum (fun a x => (hterm a x).le)
  have hSper : ∀ γ ∈ Γ, ∀ x, S (γ + x) = S x := fun γ hγ x => by
    simp only [S, hperχ _ γ hγ]
  have hSb : ∀ x, ‖S x‖ ≤ ∑' a, ‖c a‖ := fun x => by
    have hs : Summable (fun a => ‖c a * star (χ a x)‖) := by simp_rw [hterm]; exact hsum
    calc ‖S x‖ ≤ ∑' a, ‖c a * star (χ a x)‖ := norm_tsum_le_tsum_norm hs
      _ = ∑' a, ‖c a‖ := by simp_rw [hterm]
  have hcS : ∀ b, ∫ x in 𝓕, χ b x * S x ∂μ = c b := by
    intro b
    have e : ∀ x, χ b x * S x = ∑' a, χ b x * (c a * star (χ a x)) := fun x => tsum_mul_left.symm
    have hnorm : ∀ a x, ‖χ b x * (c a * star (χ a x))‖ = ‖c a‖ := fun a x => by
      rw [norm_mul, hn, one_mul, hterm]
    have hFi : ∀ a, Integrable (fun x => χ b x * (c a * star (χ a x))) (μ.restrict 𝓕) := fun a =>
      hint _ ((hc b).mul (continuous_const.mul (hc a).star)) ‖c a‖ fun x => (hnorm a x).le
    have hFs : Summable fun a => ∫ x in 𝓕, ‖χ b x * (c a * star (χ a x))‖ ∂μ := by
      simp_rw [hnorm]
      simpa [hvol] using hsum
    have e2 : ∀ a, ∫ x in 𝓕, χ b x * (c a * star (χ a x)) ∂μ = c a * (if a = b then 1 else 0) := fun a => by
      rw [← horth, ← integral_const_mul]
      congr 1
      funext x
      ring
    simp_rw [e]
    rw [← integral_tsum_of_summable_integral_norm hFi hFs]
    simp_rw [e2, mul_ite, mul_one, mul_zero]
    simp
  have hdiff := GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero G Γ K hK hcov A χ hc hx ha hχ0 hn hker
    μ 𝓕 hμ h𝓕 (Φ - S) (hΦ.sub hScont) (fun γ hγ x => by simp only [Pi.sub_apply, hper γ hγ, hSper γ hγ])
    (fun a => by
      simp only [Pi.sub_apply, mul_sub]
      have i1 : Integrable (fun x => χ a x * Φ x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hΦ) C fun x => by rw [norm_mul, hn, one_mul]; exact hΦb x
      have i2 : Integrable (fun x => χ a x * S x) (μ.restrict 𝓕) :=
        hint _ ((hc a).mul hScont) _ fun x => by rw [norm_mul, hn, one_mul]; exact hSb x
      rw [integral_sub i1 i2, hcS, sub_self])
  have h0 := congrFun hdiff 0
  simp only [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at h0
  rw [h0]
  simp only [S, hχx0, star_one, mul_one]
end GlobalTheory.CompactQuotientFourier
