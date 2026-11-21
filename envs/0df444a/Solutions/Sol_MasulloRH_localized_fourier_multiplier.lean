-- Prove2me | solution 1 for MasulloRH.localized_fourier_multiplier
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:36:49.16404+00:00
-- url     : https://prove2.me/submissions/a3aad4b5-858d-445d-9c82-4f596eebf580

import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Tactic

set_option autoImplicit false

open scoped SchwartzMap FourierTransform ContDiff
open MeasureTheory

namespace LocalizedFourier

private lemma uniformJet (f : 𝓢(ℝ, ℂ)) (p n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ i ≤ n, ∀ x : ℝ,
      (1 + |x|)^p * ‖iteratedDeriv i f x‖ ≤ C := by
  let C : ℝ := (2:ℝ)^p * (((Finset.Iic (p,n)).sup (fun t : ℕ × ℕ => SchwartzMap.seminorm ℝ t.1 t.2)) f)
  refine ⟨C, by dsimp [C]; positivity, fun i hi x => ?_⟩
  simpa only [C, schwartzSeminormFamily, Real.norm_eq_abs, norm_iteratedFDeriv_eq_norm_iteratedDeriv] using
    (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (p,n)) le_rfl hi f x)

private lemma separatedWeights (x j : ℝ) (N k : ℕ) :
    (1 + |j|)^N * |x|^k ≤ (1 + |x|)^(k+N) * (1 + |x-j|)^N := by
  have h : |j| ≤ |x| + |x-j| := by simpa [Real.norm_eq_abs] using (norm_sub_le x (x-j))
  have hj : 1 + |j| ≤ (1 + |x|) * (1 + |x-j|) := by
    nlinarith [mul_nonneg (abs_nonneg x) (abs_nonneg (x-j))]
  calc
    _ ≤ ((1+|x|)*(1+|x-j|))^N * (1+|x|)^k := by gcongr; linarith
    _ = _ := by rw [mul_pow, pow_add]; ring

private theorem boundedJets (m θ : 𝓢(ℝ, ℂ)) (N k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j x : ℝ,
      (1+|j|)^N * |x|^k * ‖iteratedDeriv n (fun u : ℝ => m u * θ (u-j)) x‖ ≤ C := by
  obtain ⟨M,hM,hderM⟩ := uniformJet m (k+N) n
  obtain ⟨B,hB,hderB⟩ := uniformJet θ N n
  use ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ) * M * B
  refine ⟨Finset.sum_nonneg fun i _ => by positivity, fun j x => ?_⟩
  have hθ : ContDiff ℝ n (fun u : ℝ => θ (u-j)) :=
    (θ.smooth n).comp (contDiff_id.sub contDiff_const)
  rw [iteratedDeriv_fun_mul (m.contDiffAt n) hθ.contDiffAt]
  simp_rw [iteratedDeriv_comp_sub_const]
  calc
    _ ≤ ((1+|j|)^N * |x|^k) *
        (∑ i ∈ Finset.range (n+1), ‖(n.choose i : ℂ) * iteratedDeriv i m x * iteratedDeriv (n-i) θ (x-j)‖) := by
      gcongr; exact norm_sum_le _ _
    _ ≤ _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i hi => ?_
      simp only [norm_mul, Complex.norm_natCast]
      have hi' : i ≤ n := Finset.mem_range_succ_iff.mp hi
      have h1 := hderM i hi' x
      have h2 := hderB (n-i) (Nat.sub_le ..) (x-j)
      calc
        _ ≤ ((1+|x|)^(k+N) * (1+|x-j|)^N) *
            ((n.choose i : ℝ) * ‖iteratedDeriv i m x‖ * ‖iteratedDeriv (n-i) θ (x-j)‖) := by
          exact mul_le_mul_of_nonneg_right (separatedWeights x j N k) (by positivity)
        _ = (n.choose i : ℝ) * ((1+|x|)^(k+N) * ‖iteratedDeriv i m x‖) *
            ((1+|x-j|)^N * ‖iteratedDeriv (n-i) θ (x-j)‖) := by ring
        _ ≤ _ := by gcongr

private noncomputable def band (m θ : 𝓢(ℝ, ℂ)) (j : ℝ) : 𝓢(ℝ, ℂ) where
  toFun u := m u * θ (u-j)
  smooth' := (m.smooth ⊤).mul ((θ.smooth ⊤).comp (contDiff_id.sub contDiff_const))
  decay' k n := by
    obtain ⟨C, _, hC⟩ := boundedJets m θ 0 k n
    exact ⟨C, fun x => by simpa only [pow_zero, one_mul, Real.norm_eq_abs,
      norm_iteratedFDeriv_eq_norm_iteratedDeriv] using hC j x⟩

private lemma bandScaled_bounded (m θ : 𝓢(ℝ,ℂ)) (N : ℕ) :
    Bornology.IsVonNBounded ℝ (Set.range (fun j : ℝ => (1+|j|)^N • band m θ j)) := by
  apply (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_seminorm_bounded.mpr
  rintro ⟨k,n⟩
  obtain ⟨C,hC,hu⟩ := boundedJets m θ N k n
  refine ⟨C+1, by positivity, ?_⟩
  rintro _ ⟨j,rfl⟩
  let w := (1+|j|)^N
  have hw : 0 < w := by dsimp [w]; positivity
  have hb : SchwartzMap.seminorm ℝ k n (band m θ j) ≤ C / w := by
    apply SchwartzMap.seminorm_le_bound' _ _ _ _ (div_nonneg hC hw.le)
    intro x
    apply (le_div_iff₀ hw).mpr
    change |x| ^ k * ‖iteratedDeriv n (fun u : ℝ => m u * θ (u-j)) x‖ * w ≤ C
    simpa only [w, mul_comm _ ((1+|j|)^N), ← mul_assoc] using hu j x
  change SchwartzMap.seminorm ℝ k n (w • band m θ j) < C + 1
  rw [map_smul_eq_mul, Real.norm_of_nonneg hw.le]
  nlinarith [(le_div_iff₀ hw).mp hb]

private lemma boundedFamily_weightedIntegral {s : Set 𝓢(ℝ,ℂ)}
    (hs : Bornology.IsVonNBounded ℝ s) (k : ℕ) :
    ∃ C : ℝ, ∀ f ∈ s, (∫ x : ℝ, (1+|x|)^k * ‖f x‖) ≤ C := by
  let p := (k+2,0)
  obtain ⟨r,hr,hsup⟩ := (schwartz_withSeminorms ℝ ℝ ℂ).isVonNBounded_iff_finset_seminorm_bounded.mp hs (Finset.Iic p)
  let C : ℝ := 2^(k+2) * r
  refine ⟨∫ x : ℝ, C / (1+|x|)^2, fun f hf => ?_⟩
  have hint : Integrable (fun x : ℝ => C / (1+|x|)^2) := by
    have h := integrable_one_add_norm (μ := (volume : Measure ℝ)) (r := (2 : ℝ)) (by norm_num)
    simpa [Real.norm_eq_abs, Real.rpow_neg (by positivity : 0 ≤ 1+|(_ : ℝ)|), div_eq_mul_inv] using h.const_mul C
  apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun x => by positivity)) hint
  refine Filter.Eventually.of_forall fun x => ?_
  have h0 := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := p) (k := k+2) (n := 0) le_rfl le_rfl f x
  simp only [Real.norm_eq_abs, norm_iteratedFDeriv_zero] at h0
  have h1 : (1+|x|)^(k+2) * ‖f x‖ ≤ C := h0.trans (mul_le_mul_of_nonneg_left (hsup f hf).le (by positivity))
  apply (le_div_iff₀ (by positivity)).mpr
  rw [pow_add] at h1
  linear_combination h1

/-- Localization of a Schwartz Fourier multiplier by translates of a fixed Schwartz window
produces inverse kernels with rapidly decreasing polynomially weighted first moments. -/
theorem weighted_inverse_fourier_band (m θ : 𝓢(ℝ,ℂ)) (k N : ℕ) :
    ∃ C : ℝ, ∀ j : ℝ, (1+|j|)^N *
        (∫ x : ℝ, (1+|x|)^k * ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-j))) x‖) ≤ C := by
  let L := FourierTransform.fourierInvCLM ℝ 𝓢(ℝ,ℂ)
  obtain ⟨C,hC⟩ := boundedFamily_weightedIntegral ((bandScaled_bounded m θ N).image L) k
  refine ⟨C, fun j => ?_⟩
  have h := hC (L ((1+|j|)^N • band m θ j)) (Set.mem_image_of_mem L (Set.mem_range_self j))
  change (∫ x : ℝ, (1+|x|)^k * ‖(𝓕⁻ ((1+|j|)^N • band m θ j)) x‖) ≤ C at h
  rw [FourierTransform.fourierInv_smul] at h
  simp only [smul_apply, norm_smul, Real.norm_of_nonneg (by positivity : 0 ≤ (1+|j|)^N)] at h
  simp only [SchwartzMap.fourierInv_coe] at h
  change (∫ x : ℝ, (1+|x|)^k * ((1+|j|)^N * ‖𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-j)) x‖)) ≤ C at h
  simpa only [← integral_const_mul, mul_left_comm ((1+|j|)^N)] using h

/-- Every polynomially weighted absolute inverse band kernel is integrable. -/
theorem integrable_inverse_fourier_band (m θ : 𝓢(ℝ,ℂ)) (j : ℝ) (k : ℕ) :
    Integrable (fun x : ℝ => (1+|x|)^k * ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-j))) x‖) := by
  let f : 𝓢(ℝ,ℂ) := 𝓕⁻ (band m θ j)
  have h : Integrable (fun x : ℝ => (1+|x|)^k * ‖f x‖) := by
    have H := (f.integrable.norm.add (f.integrable_pow_mul volume k)).const_mul ((2:ℝ)^(k-1))
    apply H.mono' (by fun_prop)
    refine Filter.Eventually.of_forall fun x => ?_
    change ‖(1 + |x|)^k * ‖f x‖‖ ≤ 2^(k-1) * (‖f x‖ + ‖x‖^k * ‖f x‖)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_eq_abs, ← one_add_mul]
    rw [← mul_assoc]
    gcongr
    simpa using add_pow_le (by norm_num : (0:ℝ) ≤ 1) (abs_nonneg x) k
  change Integrable (fun x : ℝ => (1+|x|)^k * ‖𝓕⁻ (⇑(band m θ j)) x‖)
  simpa only [f, SchwartzMap.fourierInv_coe] using h

end LocalizedFourier

theorem solution (m θ : 𝓢(ℝ, ℂ)) (k N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℝ,
      Integrable (fun x : ℝ => (1+|x|)^k * ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-j))) x‖) ∧
      (1+|j|)^N * (∫ x : ℝ, (1+|x|)^k * ‖(𝓕⁻ (fun ξ : ℝ => m ξ * θ (ξ-j))) x‖) ≤ C := by
  obtain ⟨A,hA⟩ := LocalizedFourier.weighted_inverse_fourier_band m θ k N
  exact ⟨max 0 A, le_max_left .., fun j =>
    ⟨LocalizedFourier.integrable_inverse_fourier_band m θ j k, (hA j).trans (le_max_right ..)⟩⟩
