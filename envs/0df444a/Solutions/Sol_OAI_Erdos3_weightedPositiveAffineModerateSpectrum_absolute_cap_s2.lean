-- Prove2me | solution 1 for OAI.Erdos3.weightedPositiveAffineModerateSpectrum_absolute_cap_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:30:28.592026+00:00
-- url     : https://prove2.me/submissions/cc919a3e-9f31-4454-b667-76becd470f82

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B150
import Theorems.Thm_OAI_Erdos3_weightedPositiveAffineModerate_uniform_spectrum_tail_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.LengthDyadicCutoff
namespace OAI

section

namespace Erdos3

theorem length_small_grid_bound {N V L C ζ : ℝ} {c t : ℕ}
    (hV : 0 ≤ V) (hL : 0 ≤ L)
    (hsize : N ≤ V * L ^ t) (hsmall : L ≤ C / ζ ^ c) :
    N ≤ V * C ^ t / ζ ^ (c * t) := by
  calc
    _ ≤ V * L ^ t := hsize
    _ ≤ V * (C / ζ ^ c) ^ t :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hsmall t) hV
    _ = _ := by rw [div_pow, pow_mul]; ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FrequencyGridIntervals
namespace OAI

section

namespace Erdos3

theorem frequencyGridInterval_card (M : ℕ) (center : ℝ) {radius : ℝ} (hr : 0 ≤ radius) :
    ((frequencyGridInterval M center radius).card : ℝ) ≤ 2 * radius + 1 := by
  classical
  let A := frequencyGridInterval M center radius
  have hinj : Function.Injective (fun k : Fin M => (k.val : ℤ)) := by
    intro x y h
    exact Fin.ext (Int.ofNat_inj.mp h)
  have hc := card_integer_set_le_diameter_add_one (A.image (fun k => (k.val : ℤ)))
    (by positivity : (0 : ℝ) ≤ 2 * radius) (by
      intro x hx y hy
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
      have hi' := abs_le.mp (Finset.mem_filter.mp hi).2
      have hj' := abs_le.mp (Finset.mem_filter.mp hj).2
      push_cast
      rw [abs_le]
      constructor <;> linarith)
  simpa only [Finset.card_image_of_injective _ hinj] using hc

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

theorem integerSymmetricInterval_card (B : ℕ) :
    (Finset.Icc (-(B : ℤ)) (B : ℤ)).card = 2 * B + 1 := by
  rw [Int.card_Icc]
  omega

theorem rationalGridMajorSet_card (M Q H : ℕ) :
    ((rationalGridMajorSet M Q H).card : ℝ) ≤
      (Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1) := by
  classical
  let A := Finset.Icc (-(Q * (H + 1) : ℤ)) (Q * (H + 1) : ℤ)
  have hA : (A.card : ℝ) = 2 * Q * (H + 1) + 1 := by
    have h := integerSymmetricInterval_card (Q * (H + 1))
    dsimp only [A]
    norm_cast at h ⊢
    simpa only [Nat.mul_assoc] using h
  have hd (d : ℕ) :
      ((A.biUnion fun a => frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) ≤
        (2 * Q * (H + 1) + 1) * (2 * H + 1) := by
    calc
      _ ≤ ∑ a ∈ A, ((frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ A, (2 * (H : ℝ) + 1) :=
        Finset.sum_le_sum (fun a _ => frequencyGridInterval_card M _ (Nat.cast_nonneg H))
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul, hA]
  unfold rationalGridMajorSet
  calc
    _ ≤ ∑ d ∈ Finset.range (Q + 1),
        ((A.biUnion fun a => frequencyGridInterval M ((M : ℝ) * ((a : ℝ) / d)) H).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ _d ∈ Finset.range (Q + 1), ((2 * (Q : ℝ) * (H + 1) + 1) * (2 * H + 1)) :=
      Finset.sum_le_sum (fun d _ => hd d)
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]; ring

theorem rationalGridMajorBox_card (J : Type*) [Fintype J] [DecidableEq J] (M Q H : ℕ) :
    ((rationalGridMajorBox J M Q H).card : ℝ) ≤
      ((Q + 1 : ℝ) * (2 * Q * (H + 1) + 1) * (2 * H + 1)) ^ Fintype.card J := by
  classical
  unfold rationalGridMajorBox
  rw [Fintype.card_piFinset]
  simp only [Finset.prod_const, Finset.card_univ, Nat.cast_pow]
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (rationalGridMajorSet_card M Q H) _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialGridCover
namespace OAI

section

namespace Erdos3

theorem one_le_inverse_power {C ζ : ℝ} (hC : 1 ≤ C) (hζ : 0 < ζ)
    (hζ1 : ζ ≤ 1) (r : ℕ) : 1 ≤ C / ζ ^ r := by
  apply (le_div_iff₀ (pow_pos hζ r)).mpr
  simpa only [one_mul] using (pow_le_one₀ hζ.le hζ1 : ζ ^ r ≤ 1).trans hC

theorem rationalGridMajorBox_ceil_card (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) {X : ℝ} (hX : 1 ≤ X) :
    ((rationalGridMajorBox J M ⌈X⌉₊ ⌈X⌉₊).card : ℝ) ≤
      (195 * X ^ 4) ^ Fintype.card J := by
  have hX0 : 0 ≤ X := by linarith
  have hQ0 : (0 : ℝ) ≤ ⌈X⌉₊ := Nat.cast_nonneg _
  have hQ : (⌈X⌉₊ : ℝ) ≤ 2 * X := by
    have := Nat.ceil_lt_add_one hX0
    linarith
  have hQ1 : (⌈X⌉₊ : ℝ) + 1 ≤ 3 * X := by linarith
  have hp := mul_le_mul hQ hQ1 (by positivity : 0 ≤ (⌈X⌉₊ : ℝ) + 1) (by positivity)
  have hm : 2 * (⌈X⌉₊ : ℝ) * (⌈X⌉₊ + 1) + 1 ≤ 13 * X ^ 2 := by
    nlinarith [sq_nonneg (X - 1)]
  have hr : 2 * (⌈X⌉₊ : ℝ) + 1 ≤ 5 * X := by linarith
  have hbase : ((⌈X⌉₊ : ℝ) + 1) * (2 * ⌈X⌉₊ * (⌈X⌉₊ + 1) + 1) *
      (2 * ⌈X⌉₊ + 1) ≤ 195 * X ^ 4 := by
    calc
      _ ≤ (3 * X) * (13 * X ^ 2) * (5 * X) := by gcongr
      _ = _ := by ring
  exact (rationalGridMajorBox_card J M ⌈X⌉₊ ⌈X⌉₊).trans
    (pow_le_pow_left₀ (by positivity) hbase _)

theorem polynomialGridCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M : ℕ) {C ζ : ℝ} (r : ℕ) (hC : 1 ≤ C) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ((polynomialGridCover J M C r ζ).card : ℝ) ≤
      (195 * C ^ 4) ^ Fintype.card J / ζ ^ (4 * r * Fintype.card J) := by
  have h := rationalGridMajorBox_ceil_card J M (one_le_inverse_power hC hζ hζ1 r)
  unfold polynomialGridCover
  apply h.trans_eq
  simp only [div_pow, ← mul_div_assoc, ← pow_mul]
  rw [Nat.mul_comm r 4]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem lengthAwareSpectrumCover_card {K : Type*} [Fintype K]
    (cover : ℝ → Finset K) {C L V A ζ : ℝ} {c t a : ℕ}
    (hL : 0 ≤ L) (hV : 0 ≤ V) (hA : 0 ≤ A) (hC : 0 ≤ C) (hζ : 0 < ζ)
    (hsize : (Fintype.card K : ℝ) ≤ V * L ^ t)
    (hcover : ((cover ζ).card : ℝ) ≤ A / ζ ^ a) :
    ((lengthAwareSpectrumCover C L c cover ζ).card : ℝ) ≤
      A / ζ ^ a + V * C ^ t / ζ ^ (c * t) := by
  classical
  unfold lengthAwareSpectrumCover
  split_ifs with hstart
  · exact hcover.trans (le_add_of_nonneg_right (by positivity))
  · rw [Finset.card_univ]
    have hb := length_small_grid_bound hV hL hsize (le_of_lt (lt_of_not_ge hstart))
    exact hb.trans (le_add_of_nonneg_left (by positivity))

end Erdos3

end

section

namespace Erdos3

theorem localizedMajorArcBudget_eq_power (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) :
    localizedMajorArcBudget n U ζ =
      ((denseProductDensityConstant n : ℝ) * (2 * 3 ^ n) ^ denseProductExponent n) *
        (2 * U ^ 2) ^ ((n + 1) * (2 ^ n * (denseProductExponent n + 1))) /
          ζ ^ (2 ^ n * (denseProductExponent n + 1)) := by
  unfold localizedMajorArcBudget
  rw [multiaffineBiasBudget_eq_power n (localizationThreshold_pos hU hζ (n + 1))]
  simp only [localizationThreshold, div_pow, div_div_eq_mul_div, pow_mul]

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PositiveModerateBudget
namespace OAI

section

namespace Erdos3

theorem positiveModerateLengthConstant_pos (n : ℕ) {U : ℝ} (hU : 1 ≤ U) :
    0 < positiveModerateLengthConstant n U := by
  have h0 := majorArcLengthConstant_pos n hU
  have h1 := majorArcLengthConstant_pos (n + 1) hU
  unfold positiveModerateLengthConstant
  positivity

theorem positiveModerateCoverConstant_one_le (n j : ℕ) {U V : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) : 1 ≤ positiveModerateCoverConstant n j U V := by
  have hL := majorArcLengthConstant_pos (n + 1) hU
  have hS := majorArcCoverConstant_one_le n j hU (show 0 ≤ 4 * V by positivity)
  have hT := majorArcCoverConstant_one_le (n + 1) j hU hV
  unfold positiveModerateCoverConstant
  nlinarith

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

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem positiveModerateSpectrumCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((positiveModerateSpectrumCover J M n U V L ζ).card : ℝ) ≤
      positiveModerateSpectrumConstant n (Fintype.card J) U V /
        ζ ^ positiveModerateSpectrumExponent n (Fintype.card J) +
      W * positiveModerateLengthConstant n U ^ t / ζ ^ (positiveModerateLengthExponent n * t) := by
  apply lengthAwareSpectrumCover_card _ hL hW
    (show 0 ≤ positiveModerateSpectrumConstant n (Fintype.card J) U V by
      unfold positiveModerateSpectrumConstant; positivity)
    (positiveModerateLengthConstant_pos n hU).le hζ
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · exact polynomialGridCover_card J M _ (positiveModerateCoverConstant_one_le n _ hU hV) hζ hζ1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem positiveModerateAccuracyScale_one_le (n j t : ℕ) {U V W : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) :
    1 ≤ positiveModerateAccuracyScale n j t U V W := by
  have hL := (positiveModerateLengthConstant_pos n hU).le
  have hC : 0 ≤ positiveModerateSpectrumConstant n j U V := by
    unfold positiveModerateSpectrumConstant
    positivity
  unfold positiveModerateAccuracyScale
  exact le_add_of_nonneg_right (by positivity)

theorem positiveModerateRetainedBias_spec (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    0 < positiveModerateRetainedBias n j t U V W ε ∧
    positiveModerateRetainedBias n j t U V W ε ≤ 1 ∧
    (2 * positiveModerateSpectrumConstant n j U V * 2 ^ positiveModerateSpectrumExponent n j +
      W * (2 ^ positiveModerateLengthExponent n * positiveModerateLengthConstant n U) ^ t) *
        positiveModerateRetainedBias n j t U V W ε ≤ ε := by
  have hD := positiveModerateAccuracyScale_one_le n j t (V := V) hU hW
  have hD0 : 0 < positiveModerateAccuracyScale n j t U V W := lt_of_lt_of_le zero_lt_one hD
  have hb : 0 < positiveModerateRetainedBias n j t U V W ε := div_pos hε hD0
  refine ⟨hb, (div_le_one hD0).mpr (hε1.trans hD), ?_⟩
  calc
    _ ≤ positiveModerateAccuracyScale n j t U V W *
        positiveModerateRetainedBias n j t U V W ε := by
      apply mul_le_mul_of_nonneg_right _ hb.le
      unfold positiveModerateAccuracyScale
      linarith
    _ = ε := by
      unfold positiveModerateRetainedBias
      field_simp

theorem positiveModerateSpectrumCover_card_budget (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((positiveModerateSpectrumCover J M n U V L
      (positiveModerateRetainedBias n (Fintype.card J) t U V W ε)).card : ℝ) ≤
        positiveModerateSpectrumCardBudget n (Fintype.card J) t U V W ε := by
  obtain ⟨hζ, hζ1, _⟩ := positiveModerateRetainedBias_spec n (Fintype.card J) t hU hW hε hε1
  exact positiveModerateSpectrumCover_card J M n t hU hV hW hL hζ hζ1 hsize

theorem positiveModerateSpectrum_absolute_cap {B J : Type*}
    [Fintype B] [Fintype J] [DecidableEq J]
    (M n t : ℕ) (coeff : B → (J → Fin M) → ℂ) {U V W L : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t)
    (hunit : ∀ b k, ‖coeff b k‖ ≤ 1)
    (htail : spectrumTail (positiveModerateSpectrumCover J M n U V L
      (positiveModerateRetainedBias n (Fintype.card J) t U V W 1))
        (fun k => ‖∏ b, coeff b k‖) ≤ 1) :
    (∑ k, ‖∏ b, coeff b k‖) ≤
      positiveModerateSpectrumCardBudget n (Fintype.card J) t U V W 1 + 1 := by
  exact (product_spectrum_absolute_cap coeff _ hunit).trans
    (add_le_add (positiveModerateSpectrumCover_card_budget J M n t hU hV hW hL
      zero_lt_one le_rfl hsize) htail)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedAffineModerateGridCoefficient_norm_le_one {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (shift : ℝ) (M : ℕ) (J : Finset (Finset I)) (k : J → Fin M) :
    ‖weightedAffineModerateGridCoefficient c s u v shift M J k‖ ≤ 1 := by
  let p := FiniteProbabilityWeights.pi (fun j => (s j).source)
  apply (c.source.norm_complexMean_le_mean_norm _).trans
  apply (c.source.mean_mono (fun z => ?_)).trans_eq (c.source.mean_const 1)
  exact (p.norm_complexMean_le_mean_norm _).trans_eq (by
    simp only [CircleFourier.norm_character, p.mean_const])

theorem weightedPositiveAffineModerateSpectrum_absolute_cap_s2_oai {B I : Type*}
    [Fintype B] [Fintype I] [DecidableEq I] {n : ℕ}
    (c : B → NormalizedScalarCubeSource Empty)
    (s : B → Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V W L : ℝ} {t : ℕ}
    (hU : 1 ≤ U) (hc : ∀ b, ScalarCubePrimitiveBudget (c b) A U)
    (h : ∀ b j, ScalarCubePrimitiveBudget (s b j) A U)
    (u : B → Fin (n + 1) → Option I → ℝ) (v : B → Fin (n + 1) → Option I → ℕ)
    (hv : ∀ b j i, 0 < v b j i)
    (hstride : ∀ b j i, ((v b j i * (s b j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ b z, (c b).source.weight z ≠ 0 → ((c b).length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L)
    (hlen : ∀ b j, L ≤ (s b j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : ∀ b, (M : ℝ) / (((c b).length : ℝ) * ∏ j, ((s b j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hB : positiveModerateSpectrumBlockCount n J.card t ≤ Fintype.card B)
    (hsize : (M : ℝ) ^ J.card ≤ W * L ^ t)
 :
    (∑ k, ‖∏ b, weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k‖) ≤
      positiveModerateSpectrumCardBudget n J.card t U V W 1 + 1 := by
  obtain ⟨hζ,hζ1,hacc⟩ := positiveModerateRetainedBias_spec n J.card t (V := V) hU hW
    (by norm_num : (0 : ℝ) < 1) le_rfl
  have ht := weightedPositiveAffineModerate_uniform_spectrum_tail_s2 c s A hA hU hc h u v hv hstride
    hpositive hV hW hL hζ hζ1 (by norm_num : (0 : ℝ) ≤ 1) hlen hM hscale J hJ hB hsize hacc
  have he := positiveModerateSpectrum_absolute_cap M n t
    (fun b k => weightedAffineModerateGridCoefficient (c b) (s b) (u b) (v b) 0 M J k)
    hU hV hW hL (by simpa only [Fintype.card_coe] using hsize)
    (fun b k => weightedAffineModerateGridCoefficient_norm_le_one (c b) (s b) (u b) (v b) 0 M J k)
    (by simpa only [Fintype.card_coe] using ht)
  simpa only [Fintype.card_coe] using he

end Erdos3

end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Erdos3.weightedPositiveAffineModerateSpectrum_absolute_cap_s2_oai.{u_1, u_2} := @OAI.Erdos3.weightedPositiveAffineModerateSpectrum_absolute_cap_s2_oai.{u_1, u_2}
