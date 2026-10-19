-- Prove2me | solution 1 for OAI.Erdos3.affine_weightedCube_uniform_spectrum_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:27:12.808434+00:00
-- url     : https://prove2.me/submissions/00b8d25b-50a7-4410-8a8f-d934c7e68942

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B150
import Theorems.Thm_OAI_Erdos3_polynomial_affine_weightedCubeBlock_major_arc_s2
import Theorems.Thm_OAI_Erdos3_uniformBlockSpectrumCover_polynomial_card_s2
import Theorems.Thm_OAI_Erdos3_uniformBlockSpectrum_tail_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.IndependentPhaseCoefficients
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem norm_product_coefficients_le {B : Type*} [Fintype B] (c : B → ℂ) {ζ : ℝ}
    (h : ∀ b, ‖c b‖ ≤ ζ) : ‖∏ b, c b‖ ≤ ζ ^ Fintype.card B := by
  classical
  rw [norm_prod]
  calc
    _ ≤ ∏ _b : B, ζ :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun index _ => h index)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FrequencyGridIntervals
namespace OAI

section

namespace Erdos3

theorem scaled_grid_approximation {M : ℕ} (hM : 0 < M) (k : Fin M) (a : ℤ) (d : ℕ)
    {E H : ℝ} (hclose : |(k.val : ℝ) / M - (a : ℝ) / d| ≤ E) (hE : M * E ≤ H) :
    |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H := by
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have he : (k.val : ℝ) - M * ((a : ℝ) / d) =
      (M : ℝ) * ((k.val : ℝ) / M - (a : ℝ) / d) := by field_simp
  rw [he, abs_mul, abs_of_pos hM']
  exact (mul_le_mul_of_nonneg_left hclose hM'.le).trans hE

theorem grid_approximation_numerator_bound {M Q H d : ℕ} (hM : 0 < M)
    (hd : 0 < d) (hdQ : d ≤ Q) (k : Fin M) (a : ℤ)
    (hclose : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    |a| ≤ (Q : ℤ) * (H + 1) := by
  have hM' : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hdQ' : (d : ℝ) ≤ Q := by exact_mod_cast hdQ
  have hk : (k.val : ℝ) < M := by exact_mod_cast k.isLt
  have hk0 : (0 : ℝ) ≤ k.val := Nat.cast_nonneg _
  have hH : (0 : ℝ) ≤ H := Nat.cast_nonneg _
  have hmH : (H : ℝ) ≤ M * H := le_mul_of_one_le_left hH hM'
  obtain ⟨hl, hu⟩ := abs_le.mp hclose
  have hquot : |(a : ℝ) / d| ≤ H + 1 := by
    rw [abs_le]
    constructor <;> nlinarith
  rw [abs_div, abs_of_pos hd'] at hquot
  have ha := (div_le_iff₀ hd').mp hquot
  have hbound : |(a : ℝ)| ≤ (Q : ℝ) * (H + 1) :=
    ha.trans (by nlinarith)
  exact_mod_cast hbound

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.RationalGridMajorSet
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mem_rationalGridMajorSet {M Q H d : ℕ} (hM : 0 < M) (hd : 0 < d) (hdQ : d ≤ Q)
    (k : Fin M) (a : ℤ) (hclose : |(k.val : ℝ) - M * ((a : ℝ) / d)| ≤ H) :
    k ∈ rationalGridMajorSet M Q H := by
  classical
  have ha := grid_approximation_numerator_bound hM hd hdQ k a hclose
  unfold rationalGridMajorSet
  apply Finset.mem_biUnion.mpr
  refine ⟨d, Finset.mem_range.mpr (by omega), Finset.mem_biUnion.mpr ?_⟩
  refine ⟨a, Finset.mem_Icc.mpr (abs_le.mp ha), ?_⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hclose⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridCover
namespace OAI

section

namespace Erdos3

theorem inverse_power_mono {A B ζ : ℝ} {a b : ℕ}
    (hB : 0 ≤ B) (hAB : A ≤ B) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hab : a ≤ b) :
    A / ζ ^ a ≤ B / ζ ^ b := by
  exact div_le_div₀ hB hAB (pow_pos hζ _)
    (pow_le_pow_of_le_one hζ.le hζ1 hab)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

theorem localizationLengthBudget_threshold_eq (U ζ W : ℝ) (m : ℕ) :
    localizationLengthBudget U (localizationThreshold U ζ m) W =
      256 * U ^ 6 * W * (2 * U ^ 2) ^ (m * 2) / ζ ^ 2 := by
  simp only [localizationLengthBudget, localizationThreshold, div_pow, div_div_eq_mul_div, pow_mul]

theorem localizedMajorArcBudget_eq_power (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcBudget n U ζ =
      ((denseProductDensityConstant n : ℝ) * (2 * 3 ^ n) ^ denseProductExponent n) *
        (2 * U ^ 2) ^ ((n + 1) * (2 ^ n * (denseProductExponent n + 1))) /
          ζ ^ (2 ^ n * (denseProductExponent n + 1)) := by
  unfold localizedMajorArcBudget
  rw [multiaffineBiasBudget_eq_power n (localizationThreshold_pos hU hζ (n + 1))]
  simp only [localizationThreshold, div_pow, div_div_eq_mul_div, pow_mul]

theorem localizedMajorArcLengthBudget_eq (n : ℕ) (U ζ : ℝ) :
    localizedMajorArcLengthBudget n U ζ =
      256 * U ^ 6 * (localizedMajorArcBudget n U ζ + 1) *
        (2 * U ^ 2) ^ ((n + 1) * 2) / ζ ^ 2 :=
  localizationLengthBudget_threshold_eq U ζ (localizedMajorArcBudget n U ζ + 1) (n + 1)

theorem localizedMajorArcErrorBudget_eq (n : ℕ) (U ζ : ℝ) :
    localizedMajorArcErrorBudget n U ζ =
      localizedMajorArcBudget n U ζ *
        (256 * U ^ 6 * (2 * U ^ 2) ^ ((n + 1) * 2) / ζ ^ 2) ^ (n + 1) := by
  unfold localizedMajorArcErrorBudget
  rw [localizationLengthBudget_threshold_eq]
  simp only [mul_one]

end Erdos3

end

section

namespace Erdos3

theorem majorArcBiasConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcBiasConstant n U := by
  have h := localizedMajorArcBudget_pos n hU (by norm_num : (0 : ℝ) < 1)
  rw [localizedMajorArcBudget_eq_power n hU (by norm_num)] at h
  simpa only [majorArcBiasConstant, majorArcBiasExponent, one_pow, div_one] using h

theorem majorArcLocalizationConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcLocalizationConstant n U := by
  have : 0 < U := lt_of_lt_of_le (by norm_num) hU
  unfold majorArcLocalizationConstant
  positivity

theorem majorArcLengthConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcLengthConstant n U := by
  have := majorArcBiasConstant_pos n hU
  have := majorArcLocalizationConstant_pos n hU
  unfold majorArcLengthConstant
  positivity

theorem majorArcErrorConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < majorArcErrorConstant n U := by
  have := majorArcBiasConstant_pos n hU
  have := majorArcLocalizationConstant_pos n hU
  unfold majorArcErrorConstant
  positivity

theorem localizedMajorArcBudget_constant (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcBudget n U ζ = majorArcBiasConstant n U / ζ ^ majorArcBiasExponent n :=
  localizedMajorArcBudget_eq_power n hU hζ

theorem localizedMajorArcLengthBudget_le_power (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    localizedMajorArcLengthBudget n U ζ ≤
      majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n := by
  have hp : 0 < ζ ^ majorArcBiasExponent n := pow_pos hζ _
  have hp1 : ζ ^ majorArcBiasExponent n ≤ 1 := pow_le_one₀ hζ.le hζ1
  have hone : (1 : ℝ) ≤ 1 / ζ ^ majorArcBiasExponent n := (le_div_iff₀ hp).mpr (by simpa)
  have hC := (majorArcLocalizationConstant_pos n hU).le
  rw [localizedMajorArcLengthBudget_eq, localizedMajorArcBudget_constant n hU hζ]
  have he (x : ℝ) : 256 * U ^ 6 * x * (2 * U ^ 2) ^ ((n + 1) * 2) =
      majorArcLocalizationConstant n U * x := by
    unfold majorArcLocalizationConstant
    ring
  rw [he]
  calc
    _ ≤ majorArcLocalizationConstant n U *
        (majorArcBiasConstant n U / ζ ^ majorArcBiasExponent n +
          1 / ζ ^ majorArcBiasExponent n) / ζ ^ 2 := by gcongr
    _ = _ := by
      simp only [majorArcLengthConstant, majorArcLengthExponent, pow_add]
      ring

theorem localizedMajorArcErrorBudget_constant (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcErrorBudget n U ζ =
      majorArcErrorConstant n U / ζ ^ majorArcErrorExponent n := by
  rw [localizedMajorArcErrorBudget_eq, localizedMajorArcBudget_constant n hU hζ]
  change (majorArcBiasConstant n U / ζ ^ majorArcBiasExponent n) *
    (majorArcLocalizationConstant n U / ζ ^ 2) ^ (n + 1) = _
  simp only [majorArcErrorConstant, majorArcErrorExponent, div_pow, pow_add, pow_mul]
  ring

end Erdos3

end

section

namespace Erdos3

theorem majorArcCoverConstant_one_le (n j : ℕ) {U V : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) : 1 ≤ majorArcCoverConstant n j U V := by
  have hq := (majorArcBiasConstant_pos n hU).le
  have he := (majorArcErrorConstant_pos n hU).le
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hd : 0 ≤ (majorArcBiasConstant n U * U ^ (n + 1)) ^ j := by positivity
  unfold majorArcCoverConstant
  nlinarith only [hd, mul_nonneg hV he]

theorem majorArcSpectrumConstant_nonneg (n j : ℕ) (U V : ℝ) :
    0 ≤ majorArcSpectrumConstant n j U V := by
  unfold majorArcSpectrumConstant
  positivity

theorem majorArc_denominator_le_cover (n j : ℕ) {U V ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ j ≤
      majorArcCoverConstant n j U V / ζ ^ majorArcCoverExponent n j := by
  have he := (majorArcErrorConstant_pos n hU).le
  have hC := (majorArcCoverConstant_one_le n j hU hV).trans' (by norm_num : (0 : ℝ) ≤ 1)
  have hle : (majorArcBiasConstant n U * U ^ (n + 1)) ^ j ≤
      majorArcCoverConstant n j U V := by
    unfold majorArcCoverConstant
    nlinarith only [mul_nonneg hV he]
  calc
    _ = (majorArcBiasConstant n U * U ^ (n + 1)) ^ j / ζ ^ (majorArcBiasExponent n * j) := by
      rw [localizedMajorArcBudget_constant n hU hζ, div_mul_eq_mul_div, div_pow, pow_mul]
    _ ≤ _ := inverse_power_mono hC hle hζ hζ1 (by unfold majorArcCoverExponent; omega)

theorem majorArc_scaled_error_le_cover (n j : ℕ) {U V ζ R P : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hscale : R / P ≤ V) :
    R * (localizedMajorArcErrorBudget n U ζ / P) ≤
      majorArcCoverConstant n j U V / ζ ^ majorArcCoverExponent n j := by
  have hE := (majorArcErrorConstant_pos n hU).le
  have hQ := (majorArcBiasConstant_pos n hU).le
  have hU0 : 0 ≤ U := le_trans (by norm_num) hU
  have hd : 0 ≤ (majorArcBiasConstant n U * U ^ (n + 1)) ^ j := by positivity
  have hC : 0 ≤ majorArcCoverConstant n j U V :=
    le_trans (by norm_num) (majorArcCoverConstant_one_le n j hU hV)
  have hle : V * majorArcErrorConstant n U ≤ majorArcCoverConstant n j U V := by
    unfold majorArcCoverConstant
    linarith only [hd]
  rw [localizedMajorArcErrorBudget_constant n hU hζ]
  calc
    _ = (R / P) * (majorArcErrorConstant n U / ζ ^ majorArcErrorExponent n) := by ring
    _ ≤ V * (majorArcErrorConstant n U / ζ ^ majorArcErrorExponent n) :=
      mul_le_mul_of_nonneg_right hscale (by positivity)
    _ = (V * majorArcErrorConstant n U) / ζ ^ majorArcErrorExponent n := by ring
    _ ≤ _ := inverse_power_mono hC hle hζ hζ1 (by unfold majorArcCoverExponent; omega)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumSize
namespace OAI

section

namespace Erdos3

theorem uniformBlockRetainedBias_spec (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) :
    0 < uniformBlockRetainedBias n j t U V W ε ∧
      uniformBlockRetainedBias n j t U V W ε ≤ 1 ∧
      uniformBlockSpectrumAccuracyConstant n j t U V W *
        uniformBlockRetainedBias n j t U V W ε ≤ ε := by
  have hC := (majorArcLengthConstant_pos n hU).le
  have hA := majorArcSpectrumConstant_nonneg n j U V
  have hnonneg : 0 ≤ uniformBlockSpectrumAccuracyConstant n j t U V W := by
    unfold uniformBlockSpectrumAccuracyConstant
    positivity
  have hpos : 0 < uniformBlockRetainedBias n j t U V W ε :=
    lt_min (by norm_num) (div_pos hε (by linarith))
  refine ⟨hpos, min_le_left _ _, ?_⟩
  calc
    _ ≤ (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) *
        uniformBlockRetainedBias n j t U V W ε :=
      mul_le_mul_of_nonneg_right (by linarith) hpos.le
    _ ≤ (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) *
        (ε / (uniformBlockSpectrumAccuracyConstant n j t U V W + 1)) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
    _ = ε := by field_simp

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumAbsoluteCap
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem mem_rationalGridMajorBox {J : Type*} [Fintype J] [DecidableEq J]
    {M Q H : ℕ} (hM : 0 < M) (k : J → Fin M)
    {D : ℕ} (hD : 0 < D) (hDQ : D ≤ Q) (a : J → ℤ) {E : ℝ}
    (hclose : ∀ j, |((k j).val : ℝ) / M - (a j : ℝ) / D| ≤ E)
    (hE : M * E ≤ H) : k ∈ rationalGridMajorBox J M Q H := by
  apply Fintype.mem_piFinset.mpr
  intro j
  exact mem_rationalGridMajorSet hM hD hDQ (k j) (a j)
    (scaled_grid_approximation hM (k j) (a j) (D) (hclose j) hE)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical
open CircleFourier

theorem gridJetFrequency_apply {I : Type*} [DecidableEq I]
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) (S : J) :
    gridJetFrequency M J k S = ((k S).val : ℝ) / M := by
  simp only [gridJetFrequency, dif_pos S.property]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem sum_eq_retained_add_spectrumTail {K : Type*} [Fintype K] [DecidableEq K]
    (S : Finset K) (f : K → ℝ) : ∑ k, f k = (∑ k ∈ S, f k) + spectrumTail S f := by
  calc
    _ = ∑ k, ((if k ∈ S then f k else 0) + (if k ∈ S then 0 else f k)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hk : k ∈ S <;> simp only [hk, ite_true, ite_false, add_zero, zero_add]
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, spectrumTail]

theorem product_spectrum_absolute_cap {B K : Type*} [Fintype B] [Fintype K] [DecidableEq K]
    (c : B → K → ℂ) (S : Finset K) (hunit : ∀ b k, ‖c b k‖ ≤ 1) :
    (∑ k, ‖∏ b, c b k‖) ≤ S.card + spectrumTail S (fun k => ‖∏ b, c b k‖) := by
  rw [sum_eq_retained_add_spectrumTail S]
  refine add_le_add ?_ le_rfl
  calc
    _ ≤ ∑ _k ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro k _
      simpa only [one_pow] using norm_product_coefficients_le (fun b => c b k) (fun b => hunit b k)
    _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniformBlockSpectrum_absolute_cap {B J : Type*} [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hB : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hunit : ∀ b k, ‖coeff b k‖ ≤ 1)
    (hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖coeff b k‖ ≤ δ) :
    (∑ k, ‖∏ b, coeff b k‖) ≤ uniformSpectrumAbsoluteCap n (Fintype.card J) t U V W := by
  classical
  obtain ⟨hζ, hζ1, hacc⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW (by norm_num : (0 : ℝ) < 1)
  let S := uniformBlockSpectrumCover J M n U V L (uniformBlockRetainedBias n (Fintype.card J) t U V W 1)
  have ht := uniformBlockSpectrum_tail_s2 M n t coeff hU hV hW hL hζ hζ1 (by norm_num) hB hsize hminor hacc
  have hc : (S.card : ℝ) ≤ uniformSpectrumSizeConstant n (Fintype.card J) t U V W := by
    simpa only [one_pow, div_one] using uniformBlockSpectrumCover_polynomial_card_s2 J M n t
      hU hV hW hL (by norm_num : (0 : ℝ) < 1) le_rfl hsize
  exact (product_spectrum_absolute_cap coeff S hunit).trans (add_le_add hc ht)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AffineBlockScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators
open CircleFourier

theorem affineWeightedCubeGridCoefficient_norm_le_one {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    ‖affineWeightedCubeGridCoefficient s u v M J k‖ ≤ 1 := by
  let p := FiniteProbabilityWeights.pi (fun j => (s j).source)
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by simp only [norm_character, p.mean_const])

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affineWeightedCubeGridCoefficient_mem_cover {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤ (s j).length)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    {M : ℕ} (hM : 0 < M) (hscale : (M : ℝ) / ∏ j, ((s j).length : ℝ) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : ζ ≤ ‖affineWeightedCubeGridCoefficient s u v M J k‖) :
    k ∈ polynomialGridCover J M (majorArcCoverConstant n J.card U V) (majorArcCoverExponent n J.card) ζ := by
  have hU := (h 0).one_le
  obtain ⟨D, hD, hDb, a, ha⟩ := polynomial_affine_weightedCubeBlock_major_arc_s2 s A hA h hζ hζ1
    (fun j => (localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans (hlen j))
    u v hv hstride (gridJetFrequency M J k) J hJ hk
  have hQ := (majorArc_denominator_le_cover n J.card hU hV hζ hζ1).trans (Nat.le_ceil _)
  have hH := (majorArc_scaled_error_le_cover n J.card hU hV hζ hζ1 hscale).trans (Nat.le_ceil _)
  apply mem_rationalGridMajorBox hM k hD (by exact_mod_cast hDb.trans hQ) a _ hH
  intro S
  simpa only [gridJetFrequency_apply] using ha S

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AffineUniformSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem affine_weightedCube_uniform_spectrum_s2_oai {B I : Type*} [Fintype B] [Fintype I] [DecidableEq I]
    {n : ℕ} (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U) (hlen : ∀ b j, L ≤ (s b j).length)
    (hv : ∀ b j i, 0 < v b j i) (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (M t : ℕ) (hM : 0 < M) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : uniformSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
    (hscale : ∀ b, (M : ℝ) / ∏ j, ((s b j).length : ℝ) ≤ V) :
    let ζ := uniformBlockRetainedBias n J.card t U V W ε
    let S := uniformBlockSpectrumCover J M n U V L ζ
    spectrumTail S (fun k => ‖∏ b, affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J k‖) ≤ ε ∧
      (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J k‖) ≤
        uniformSpectrumAbsoluteCap n J.card t U V W := by
  let c b := affineWeightedCubeGridCoefficient (s b) (u b) (v b) M J
  have hminor : ∀ δ, 0 < δ → δ ≤ 1 → majorArcLengthConstant n U / δ ^ majorArcLengthExponent n ≤ L →
      ∀ b k, k ∉ polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
        (majorArcCoverExponent n (Fintype.card J)) δ → ‖c b k‖ ≤ δ := by
    intro δ hδ hδ1 hlength b k hk
    apply le_of_lt (lt_of_not_ge (fun hh => hk ?_))
    simpa only [Fintype.card_coe] using affineWeightedCubeGridCoefficient_mem_cover (s b) A hA (h b)
      hV hδ hδ1 (fun j => hlength.trans (hlen b j)) (u b) (v b) (hv b) (hstride b)
      hM (hscale b) J hJ k hh
  have hB' : uniformSpectrumBlockCount n (Fintype.card J) t ≤ Fintype.card B := by simpa only [Fintype.card_coe] using hB
  have hsize' : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t := by simpa only [Fintype.card_coe] using hsize
  obtain ⟨hζ, hζ1, hacc⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW hε
  constructor
  · simpa only [c, Fintype.card_coe] using uniformBlockSpectrum_tail_s2 M n t c hU hV hW hL
      hζ hζ1 hε.le hB' hsize' hminor hacc
  · simpa only [c, Fintype.card_coe] using uniformBlockSpectrum_absolute_cap M n t c hU hV hW hL
      hB' hsize' (fun b k => affineWeightedCubeGridCoefficient_norm_le_one (s b) (u b) (v b) M J k) hminor

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.affine_weightedCube_uniform_spectrum_s2_oai.{u_1, u_2} := @OAI.Erdos3.affine_weightedCube_uniform_spectrum_s2_oai.{u_1, u_2}
