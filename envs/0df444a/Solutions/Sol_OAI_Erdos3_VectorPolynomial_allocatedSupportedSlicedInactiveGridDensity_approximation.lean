-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveGridDensity_approximation
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-09T17:10:36.561978+00:00
-- url     : https://prove2.me/submissions/32d92dd9-da17-482d-8338-abd0a8956946

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIErdos3B145
import Theorems.Thm_OAI_Erdos3_affine_weightedCube_grid_density
import Theorems.Thm_OAI_Erdos3_affine_weightedCube_uniform_spectrum
import Theorems.Thm_OAI_Erdos3_containedSupportedProgressionLaw_axis_integer_law

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

theorem inverse_power_mono {A B ζ : ℝ} {a b : ℕ}
    (hB : 0 ≤ B) (hAB : A ≤ B) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hab : a ≤ b) :
    A / ζ ^ a ≤ B / ζ ^ b := by
  exact div_le_div₀ hB hAB (pow_pos hζ _)
    (pow_le_pow_of_le_one hζ.le hζ1 hab)

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

end Erdos3

end

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

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

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

theorem majorArcSpectrumConstant_nonneg (n j : ℕ) (U V : ℝ) :
    0 ≤ majorArcSpectrumConstant n j U V := by
  unfold majorArcSpectrumConstant
  positivity

theorem uniformMajorArcCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n : ℕ) {U V ζ : ℝ} (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    ((polynomialGridCover J M (majorArcCoverConstant n (Fintype.card J) U V)
      (majorArcCoverExponent n (Fintype.card J)) ζ).card : ℝ) ≤
      majorArcSpectrumConstant n (Fintype.card J) U V /
        ζ ^ majorArcSpectrumExponent n (Fintype.card J) :=
  polynomialGridCover_card J M _ (majorArcCoverConstant_one_le n _ hU hV) hζ hζ1

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem uniformBlockSpectrumCover_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((uniformBlockSpectrumCover J M n U V L ζ).card : ℝ) ≤
      uniformBlockSpectrumCardBudget n (Fintype.card J) t U V W ζ := by
  apply lengthAwareSpectrumCover_card _ hL hW (majorArcSpectrumConstant_nonneg _ _ _ _)
    (majorArcLengthConstant_pos n hU).le hζ
  · simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hsize
  · exact uniformMajorArcCover_card J M n hU hV hζ hζ1

end Erdos3

end

section

namespace Erdos3

end Erdos3

end

section

namespace Erdos3

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

section

namespace Erdos3

theorem uniformBlockRetainedBias_eq (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε1 : ε ≤ 1) :
    uniformBlockRetainedBias n j t U V W ε =
      ε / (uniformBlockSpectrumAccuracyConstant n j t U V W + 1) := by
  have hC := (majorArcLengthConstant_pos n hU).le
  have hA := majorArcSpectrumConstant_nonneg n j U V
  have hnonneg : 0 ≤ uniformBlockSpectrumAccuracyConstant n j t U V W := by
    unfold uniformBlockSpectrumAccuracyConstant
    positivity
  apply min_eq_right
  apply (div_le_iff₀ (by linarith)).mpr
  linarith

theorem uniformBlockSpectrumCardBudget_le_accuracy_power (n j t : ℕ) {U V W ε : ℝ}
    (hU : 1 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    uniformBlockSpectrumCardBudget n j t U V W (uniformBlockRetainedBias n j t U V W ε) ≤
      uniformSpectrumSizeConstant n j t U V W /
        ε ^ max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) := by
  obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n j t hU hW hε
  have hC := (majorArcLengthConstant_pos n hU).le
  have hA := majorArcSpectrumConstant_nonneg n j U V
  have hb : 0 ≤ W * majorArcLengthConstant n U ^ t := by positivity
  have ha := inverse_power_mono hA le_rfl hζ hζ1
    (le_max_left (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t))
  have hp := inverse_power_mono hb le_rfl hζ hζ1
    (le_max_right (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t))
  unfold uniformBlockSpectrumCardBudget
  apply (add_le_add ha hp).trans_eq
  rw [← add_div, uniformBlockRetainedBias_eq n j t hU hW hε1]
  simp only [uniformSpectrumSizeConstant, div_pow, div_div_eq_mul_div]

theorem uniformBlockSpectrumCover_polynomial_card (J : Type*) [Fintype J] [DecidableEq J]
    (M n t : ℕ) {U V W L ε : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hL : 0 ≤ L) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (M : ℝ) ^ Fintype.card J ≤ W * L ^ t) :
    ((uniformBlockSpectrumCover J M n U V L
      (uniformBlockRetainedBias n (Fintype.card J) t U V W ε)).card : ℝ) ≤
      uniformSpectrumSizeConstant n (Fintype.card J) t U V W /
        ε ^ max (majorArcSpectrumExponent n (Fintype.card J)) (majorArcLengthExponent n * t) := by
  obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n (Fintype.card J) t hU hW hε
  exact (uniformBlockSpectrumCover_card J M n t hU hV hW hL hζ hζ1 hsize).trans
    (uniformBlockSpectrumCardBudget_le_accuracy_power n (Fintype.card J) t hU hW hε hε1)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.ProductPMFMap
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem dependentProductPMF_apply {D : Type*} [Fintype D] {X : D → Type*}
    [∀ d, Countable (X d)] [∀ d, MeasurableSpace (X d)] [∀ d, MeasurableSingletonClass (X d)]
    (p : ∀ d, PMF (X d)) (x : ∀ d, X d) : dependentProductPMF p x = ∏ d, p d (x d) := by
  simp only [dependentProductPMF, Measure.toPMF_apply, Measure.pi_singleton]
  exact Finset.prod_congr rfl (fun d _ => (p d).toMeasure_apply_singleton (x d) (measurableSet_singleton _))

end Erdos3

end

section

namespace Erdos3
open MeasureTheory

theorem dependentProductPMF_map {J : Type*} [Fintype J] {X Y : J → Type*}
    [∀ j, Countable (X j)] [∀ j, MeasurableSpace (X j)] [∀ j, MeasurableSingletonClass (X j)]
    [∀ j, Countable (Y j)] [∀ j, MeasurableSpace (Y j)] [∀ j, MeasurableSingletonClass (Y j)]
    (p : ∀ j, PMF (X j)) (f : ∀ j, X j → Y j) :
    (dependentProductPMF p).map (fun x j => f j (x j)) =
      dependentProductPMF (fun j => (p j).map (f j)) := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [dependentProductPMF, Measure.toPMF_toMeasure]
  rw [Measure.pi_map_pi (fun j => (measurable_of_countable (f j)).aemeasurable)]
  congr 1
  funext j
  exact PMF.toMeasure_map (f j) (p j) (measurable_of_countable _)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarCubeLatticeGeometry
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

theorem scalarCubeValue_sub_bound {I : Type*} [Fintype I] [DecidableEq I]
    (x y : Option I → ℝ) {δ : ℝ} (hδ : 0 ≤ δ) (he : ‖x-y‖ ≤ δ) (t : Finset I) :
    |scalarCubeValue x t - scalarCubeValue y t| ≤ (Fintype.card I + 1 : ℝ)*δ := by
  have hi (i : Option I) : |x i-y i| ≤ δ := (norm_le_pi_norm (x-y) i).trans he
  have hsum : |∑ i ∈ t, (x (some i)-y (some i))| ≤ (t.card : ℝ)*δ := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    simpa only [Finset.sum_const, nsmul_eq_mul] using Finset.sum_le_sum (fun i (_ : i ∈ t) => hi (some i))
  have hcard : (t.card : ℝ) ≤ Fintype.card I := by exact_mod_cast t.card_le_univ
  have hid : scalarCubeValue x t - scalarCubeValue y t =
      (x none-y none) + ∑ i ∈ t, (x (some i)-y (some i)) := by
    simp only [scalarCubeValue_formula, Finset.sum_sub_distrib]
    ring
  rw [hid]
  exact (abs_add_le _ _).trans ((add_le_add (hi none) hsum).trans (by nlinarith))

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeDensityBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeInnerBox_subset (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeInnerBox I ⊆ scalarCubeDomain I := by
  intro x hx t
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have hn : ‖x-scalarCubeCenter I‖ ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by
    apply (pi_norm_le_iff_of_nonneg hr).mpr
    intro i
    change |x i-scalarCubeCenter I i| ≤ _
    exact abs_le.mpr ⟨by linarith [hx.1 i], by linarith [hx.2 i]⟩
  have hb := scalarCubeValue_sub_bound x (scalarCubeCenter I) hr hn t
  rw [scalarCubeValue_center] at hb
  have he : ((Fintype.card I : ℝ)+1)*(1/(4*((Fintype.card I : ℝ)+1))) = 1/4 := by
    field_simp
  rw [he] at hb
  have ha := abs_le.mp hb
  exact ⟨by linarith [ha.1], by linarith [ha.2]⟩

theorem scalarCubeInnerBox_volume (I : Type*) [Fintype I] :
    volume.real (scalarCubeInnerBox I) = (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by
  have hr : 0 ≤ 1/(4*((Fintype.card I : ℝ)+1)) := by positivity
  have ho : (fun i => scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) ≤
      (fun i => scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))) := fun i => by linarith
  have he (i : Option I) : scalarCubeCenter I i+1/(4*((Fintype.card I : ℝ)+1))-
      (scalarCubeCenter I i-1/(4*((Fintype.card I : ℝ)+1))) = 1/(2*((Fintype.card I : ℝ)+1)) := by
    field_simp
    ring
  simp only [measureReal_def, scalarCubeInnerBox, Real.volume_Icc_pi_toReal ho, he,
    Finset.prod_const, Finset.card_univ, Fintype.card_option]

theorem scalarCubeDomainDensity_le_power (I : Type*) [Fintype I] [DecidableEq I] :
    scalarCubeDomainDensity I ≤ (2*((Fintype.card I : ℝ)+1))^(Fintype.card I+1) := by
  have hv := measureReal_mono (scalarCubeInnerBox_subset I) (scalarCubeDomain_volume_lt_top I).ne
  rw [scalarCubeInnerBox_volume] at hv
  have hp : 0 < (1/(2*((Fintype.card I : ℝ)+1)))^(Fintype.card I+1) := by positivity
  have hi := one_div_le_one_div_of_le hp hv
  simpa only [scalarCubeDomainDensity, one_div, inv_pow, inv_inv] using hi

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.FiniteDependentPMFBind
namespace OAI

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators Classical

variable {X : Type*} [Fintype X]

theorem toPMF_bind_apply {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    (p.toPMF.bind q) y = ∑ x, ENNReal.ofReal (p.weight x) * q x y := by
  rw [PMF.bind_apply, tsum_fintype]
  simp only [toPMF_apply]

theorem toPMF_bind_toReal {Y : Type*} (p : FiniteProbabilityWeights X)
    (q : X → PMF Y) (y : Y) :
    ((p.toPMF.bind q) y).toReal = p.mean (fun x => (q x y).toReal) := by
  rw [toPMF_bind_apply, ENNReal.toReal_sum (fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ((q x).apply_ne_top y))]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (p.nonneg _), mean]

theorem toPMF_pi {J : Type*} [Fintype J] {Ω : J → Type*} [∀ j, Fintype (Ω j)]
    [∀ j, MeasurableSpace (Ω j)] [∀ j, MeasurableSingletonClass (Ω j)]
    (p : ∀ j, FiniteProbabilityWeights (Ω j)) :
    (pi p).toPMF = Erdos3.dependentProductPMF (fun j => (p j).toPMF) := by
  ext x
  rw [toPMF_apply, Erdos3.dependentProductPMF_apply]
  change ENNReal.ofReal (∏ j, (p j).weight (x j)) = ∏ j, ENNReal.ofReal ((p j).weight (x j))
  exact ENNReal.ofReal_prod_of_nonneg (fun j _ => (p j).nonneg (x j))

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights
open scoped BigOperators Classical

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

end Erdos3.FiniteProbabilityWeights

end

section

namespace Erdos3

open scoped BigOperators Classical

namespace FiniteProbabilityWeights

end FiniteProbabilityWeights

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.IntegerPMFNormalizedSource
namespace OAI

section

namespace Erdos3

open scoped BigOperators NNReal Classical

namespace FiniteProbabilityWeights

theorem toPMF_map_toReal {X Y : Type*} [Fintype X] (p : FiniteProbabilityWeights X)
    (f : X → Y) (y : Y) :
    ((p.toPMF.map f) y).toReal = p.mean (fun x => if f x = y then 1 else 0) := by
  change ((p.toPMF.bind (fun x => PMF.pure (f x))) y).toReal = _
  rw [toPMF_bind_toReal]
  congr 1
  funext x
  by_cases h : f x = y
  · simp [PMF.pure_apply, h]
  · have h' : y ≠ f x := Ne.symm h
    simp [PMF.pure_apply, h, h']

end FiniteProbabilityWeights

section IntegerSourceLaw

variable (L : ℕ) (hL : 0 < L) (p : PMF ℤ)
variable (hs : ∀ k, p k ≠ 0 → k ∈ Finset.Ico 0 (L : ℤ))
variable (w : (Option Empty → ℝ) → ℝ) (B T : ℝ≥0) (hB : 0 < B)
variable (hw : ∀ x, 0 ≤ w x ∧ w x ≤ B) (hLip : LipschitzWith T w)
variable (hgrid : ∀ k : ℤ, w (fun _ => (k : ℝ) / L) = L * (p k).toReal)

local notation "intervalSource" =>
  normalizedScalarCubeSourceOfIntegerPMF L hL p hs w B T hB hw hLip hgrid

end IntegerSourceLaw

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CanonicalScalarSourceEnvelope
namespace OAI

section

namespace Erdos3

open scoped NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

end Erdos3

end

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem paddedResidueDensityCap_mono (I : Type*) [Fintype I] {M N : ℕ} (hMN : M ≤ N) :
    paddedResidueDensityCap I M ≤ paddedResidueDensityCap I N := by
  unfold paddedResidueDensityCap scalarCubeResidueDensityCap
  gcongr

theorem ScalarCubePrimitiveBudget.mono {I : Type*} [Fintype I] [DecidableEq I]
    {s : NormalizedScalarCubeSource I} {A : ℝ≥0} {U V : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hUV : U ≤ V) : ScalarCubePrimitiveBudget s A V :=
  ⟨h.one_le.trans hUV, h.dimension_le.trans hUV, h.modulus_le.trans hUV,
    h.weight_le.trans hUV, h.weightLipschitz_le.trans hUV, h.boundary_le.trans hUV,
    h.grid_le.trans hUV, h.derivative_le.trans hUV, h.density_le.trans hUV⟩

theorem scalarCubePrimitiveBudget_of_raw_bounds {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A B T : ℝ≥0) (M : ℕ)
    (hM : s.modulusBound ≤ M) (hB : s.weightBound ≤ B) (hT : s.weightLipschitz ≤ T) :
    ScalarCubePrimitiveBudget s A (scalarCubePrimitiveEnvelope I A B T M) := by
  let q := (Fintype.card I : ℝ) + 1
  let V := (2 * q) ^ (Fintype.card I + 1)
  let X := 4 * V * ((2 : ℝ) ^ Fintype.card I) ^ 2
  let Y := 2 * scalarCubeGridBoundaryConstant I * V
  have hq : 0 ≤ q := by dsimp only [q]; positivity
  have hX : 0 ≤ X := by dsimp only [X, V]; positivity
  have hY : 0 ≤ Y := by dsimp only [Y, V, scalarCubeGridBoundaryConstant]; positivity
  have hZ : 0 ≤ scalarCubeCutoffDerivativeNumerator I A := by
    unfold scalarCubeCutoffDerivativeNumerator; positivity
  have hP : 0 ≤ paddedResidueDensityCap I M := by
    unfold paddedResidueDensityCap scalarCubeResidueDensityCap; positivity
  have hparts :
      1 ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      q ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (M : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (B : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      (T : ℝ) ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      X ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      Y ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ scalarCubePrimitiveEnvelope I A B T M ∧
      paddedResidueDensityCap I M ≤ scalarCubePrimitiveEnvelope I A B T M := by
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧ _
    dsimp only [scalarCubePrimitiveEnvelope]
    change 1 ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      q ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (M : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (B : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      (T : ℝ) ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      X ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      Y ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      scalarCubeCutoffDerivativeNumerator I A ≤ 1 + q + M + B + T + X + Y + _ + _ ∧
      paddedResidueDensityCap I M ≤ 1 + q + M + B + T + X + Y + _ + _
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      linarith only [hq, hX, hY, hZ, hP, Nat.cast_nonneg (α := ℝ) M, B.coe_nonneg, T.coe_nonneg]
  obtain ⟨h1, hq', hM', hB', hT', hX', hY', hZ', hP'⟩ := hparts
  have hvol : scalarCubeDomainDensity I ≤ V := scalarCubeDomainDensity_le_power I
  have hboundary : scalarCubeBoundaryConstant I ≤ X := by
    unfold scalarCubeBoundaryConstant
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hvol (by norm_num)) (by positivity)
  have hgrid : 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) ≤ Y := by
    have hh := mul_le_mul_of_nonneg_left hvol
      (show 0 ≤ 2 * scalarCubeGridBoundaryConstant I by unfold scalarCubeGridBoundaryConstant; positivity)
    simpa only [scalarCubeDomainDensity, div_eq_mul_inv, Y] using hh
  refine ⟨h1, hq', ?_, ?_, ?_, hboundary.trans hX', hgrid.trans hY', hZ', ?_⟩
  · exact (by exact_mod_cast hM : (s.modulusBound : ℝ) ≤ M).trans hM'
  · exact (by exact_mod_cast hB : (s.weightBound : ℝ) ≤ B).trans hB'
  · exact (by exact_mod_cast hT : (s.weightLipschitz : ℝ) ≤ T).trans hT'
  · exact (paddedResidueDensityCap_mono I hM).trans hP'

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

theorem normalizedUniformCubeSource_primitive (I : Type*) [Fintype I] [DecidableEq I]
    (L M : ℕ) (hL : 0 < L) (m : Option I → ℕ) (r : ∀ i, ZMod (m i))
    (hm : ∀ i, 0 < m i) (hmM : ∀ i, m i ≤ M) (hsize : (Fintype.card I + 1) * M ≤ L) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget (normalizedUniformCubeSource I L M hL m r hm hmM hsize) A
      (scalarCubePrimitiveEnvelope I A 1 0 M) :=
  scalarCubePrimitiveBudget_of_raw_bounds _ A 1 0 M le_rfl le_rfl le_rfl

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

variable {K T γ : ℝ} (hK : 0 < K) (hT : 0 < T) (hγ : 0 < γ)
variable (hlarge : 8 * (probabilityProfileLipschitz : ℝ) ≤ (γ / 2) * (K / T))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.InactiveAxisScale
namespace OAI

section

namespace Erdos3

theorem inactiveSideLength_lower_power {h K q : ℕ} (hh : 0 < h) (hq : 0 < q)
    (hlarge : 2 * q ≤ K) : K < q * 2 ^ h * inactiveSideLength h K q ^ h := by
  have hpos := inactiveSideLength_pos (K := K) hh hq
  have hnext : K / q < (inactiveSideLength h K q + 1) ^ h := by
    simpa [inactiveSideLength, hlarge] using Nat.lt_pow_nthRoot_add_one hh.ne' (K / q)
  have hdiv : K < q * (K / q + 1) := by
    have hm := Nat.mod_lt K hq
    have he := Nat.mod_add_div K q
    nlinarith
  calc
    K < q * (K / q + 1) := hdiv
    _ ≤ q * (inactiveSideLength h K q + 1) ^ h :=
      Nat.mul_le_mul_left q (Nat.succ_le_of_lt hnext)
    _ ≤ q * (2 * inactiveSideLength h K q) ^ h := by gcongr; omega
    _ = _ := by rw [mul_pow]; ring

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.WeightedModeratePointMass
namespace OAI

section

namespace Erdos3

open scoped Classical

theorem finiteImageMass_eq_toPMF {X H : Type*} [Fintype X] [DecidableEq H]
    (p : FiniteProbabilityWeights X) (Y : X → H) (z : H) :
    finiteImageMass p Y z = ((p.toPMF.map Y) z).toReal := by
  have he : finiteImageMass p Y z = p.mean (fun x =>
      @ite ℝ (Y x = z) (Classical.propDecidable (Y x = z)) 1 0) := by
    unfold finiteImageMass
    apply congrArg (fun f : X → ℝ => p.mean f)
    funext x
    by_cases hx : Y x = z <;> simp [hx]
  exact he.trans (FiniteProbabilityWeights.toPMF_map_toReal p Y z).symm

theorem integerGridMass_eq_toPMF {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z =
      ((p.toPMF.map (fun x => integerGridResidue M (Y x))) (integerGridResidue M z)).toReal :=
  finiteImageMass_eq_toPMF p (fun x => integerGridResidue M (Y x)) (integerGridResidue M z)

theorem integerGridMass_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (M : ℕ) (z : J → ℤ) :
    integerGridMass p Y M z = ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal := by
  have ht : p.toPMF.map (fun x => integerGridResidue M (Y x)) = μ.map (integerGridResidue M) :=
    (PMF.map_comp Y p.toPMF (integerGridResidue M)).symm.trans
      (congrArg (fun ν : PMF (J → ℤ) => ν.map (integerGridResidue M)) hμ)
  exact (integerGridMass_eq_toPMF p Y M z).trans
    (congrArg (fun ν : PMF (J → ZMod M) => (ν (integerGridResidue M z)).toReal) ht)

theorem integerGridDensity_eq_of_pmf_image {X J : Type*} [Fintype X] [Fintype J] [DecidableEq J]
    (p : FiniteProbabilityWeights X) (Y : X → J → ℤ) (μ : PMF (J → ℤ))
    (hμ : p.toPMF.map Y = μ) (K M : ℕ) (z : J → ℤ) :
    integerGridDensity p Y K M z =
      (K : ℝ) ^ Fintype.card J * ((μ.map (integerGridResidue M)) (integerGridResidue M z)).toReal :=
  congrArg (fun t : ℝ => (K : ℝ) ^ Fintype.card J * t)
    (integerGridMass_eq_of_pmf_image p Y μ hμ M z)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {B I : Type*} [Fintype B] [DecidableEq B] [Fintype I] [DecidableEq I]
variable {n K M : ℕ}
variable (c : B → NormalizedScalarCubeSource Empty) (s : B → Fin n → NormalizedScalarCubeSource I)
variable (offset : B → ℤ)

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedResidueInterpolationMixture
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "coord" => principalSupportedCoordinateWeights B h L hL q r hcell
local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3

end

section

namespace Erdos3

open scoped Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ t, 0 < L t)
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (a : D) (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ L ⟨a, b, v⟩)

local notation "sources" => principalSupportedAxisSources B h L hL q hq r a hsize

omit [Fintype D] [DecidableEq D] [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] in
theorem principalSupportedAxisSources_primitive (b : B a) (v : Fin (h a)) (A : ℝ≥0) :
    ScalarCubePrimitiveBudget ((sources) b v) A (scalarCubePrimitiveEnvelope α A 1 0 q) :=
  normalizedUniformCubeSource_primitive α (L ⟨a, b, v⟩) q (hL ⟨a, b, v⟩) (fun _ => q)
    (r ⟨a, b, v⟩) (fun _ => hq) (fun _ => le_rfl) (hsize b v) A

variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
variable (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h L hL).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "conditioned" => FiniteProbabilityWeights.condition (principalTupleWeights (α := α) B h L hL)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)

local notation "sides" => allocatedPrincipalSides B U basis S
local notation "sides_pos" => allocatedPrincipalSides_pos B U basis S

variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j))
variable (hactive : S.value ^ (j.val + 1) < basisAxisScale (basis j) i)
variable (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : (Fintype.card α + 1) * q ≤ S.value)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S)).mass
    (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => FiniteProbabilityWeights.condition
  (principalTupleWeights B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) (allocatedPrincipalSides_pos B U basis S))
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell

local notation "constantLaw" => allocatedLayerIntegerPMFs B U basis hR hσ S j i
  (principalCoefficientChoice (G := G) (layerSamplerDegree I n) (Sigma.mk j (Sum.inr i)) none)

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.AllocatedInactiveResidueScale
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

variable (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedInactivePrincipalPMF
    (hsmall : basisAxisScale (b j) i ≤ S.value ^ (j.val + 1)) (a : B ⟨j, Sum.inr i⟩) :
    allocatedLayerIntegerPMFs B U b hR hσ S j i
      (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a) =
    PMF.pure (inactivePrincipalCoefficient (basisAxisScale (b j) i)
      (inactiveDenominator (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card))) := by
  have hmem : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ∈
      layerIntegerPrincipalSlots (G := G) B j i := (mem_principalCoefficientSlots _ _ _).mpr ⟨a, rfl⟩
  have hne : principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a ≠
      constantCoefficientSlot (LayerSamplerVariables G I n B) (j.val + 1) := by
    intro he
    exact (layerIntegerPrincipalSlots_not_constant B j i) (he ▸ hmem)
  simp only [allocatedLayerIntegerPMFs, allocatedProjectionPMFs,
    allocatedIntegerPolynomialCoordinatePMF, integerPolynomialCoordinatePMF]
  split_ifs with hc hp
  · exact False.elim (hne hc)
  · exact integerAxisPrincipalPMF_inactive (Nat.zero_lt_succ _)
      (basisAxisScale_pos (b j) i) S.positive (principalProfileSize_pos (hR j) _) (S.gap j i) hsmall
  · exact False.elim (hp hmem)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (j : Fin m) (i : Fin (n j)) (q : ℕ) (hq : 0 < q)
variable (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hsize : ∀ (a : B ⟨j, Sum.inr i⟩) (v : Fin (j.val + 1)),
  (Fintype.card α + 1) * q ≤ allocatedPrincipalSides B U b S ⟨⟨j, Sum.inr i⟩, a, v⟩)

local notation "height" => basisAxisScale (b j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ContainedSupportedProgressionJetLaw
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆ Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "weights" => FiniteProbabilityWeights.condition (principalTupleWeights B h H hH)
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)) hcell
local notation "tupleMap" => containedProgressionTupleMap B h L H step c hL hsubset

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

variable {D α : Type*} [Fintype D] [DecidableEq D] [Fintype α] [DecidableEq α]
variable (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)] (h : D → ℕ)
variable (L H step : PrincipalTupleIndex B h → ℕ) (c : PrincipalTupleIndex B h → ℤ)
variable (hL : ∀ j, 0 < L j) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (L j : ℤ))
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B h → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B h H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

local notation "law" => containedSupportedProgressionLaw B h L H step c hL hH hsubset q r hcell

theorem containedSupportedProgressionLaw_unit_block_law (a : D)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨a,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B h H hH q hq r a hsize
    (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (sources b v).source))).toPMF.map
      (fun z => shift + ∑ b, fun t : rows => integerBooleanBlockJet
        (fun v k => (if k = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (z b v k : ℤ)) t) =
      (law).toPMF.map (fun y => shift + ∑ b, fun t : rows =>
        integerBooleanBlockJet (fun v k => (y ⟨a,b,v⟩ k : ℤ)) t) := by
  intro sources
  have houter :
      (FiniteProbabilityWeights.pi (fun b => FiniteProbabilityWeights.pi (fun v => (sources b v).source))).toPMF =
        dependentProductPMF (fun b => (FiniteProbabilityWeights.pi (fun v => (sources b v).source)).toPMF) :=
    FiniteProbabilityWeights.toPMF_pi _
  have hinner (b : B a) : (FiniteProbabilityWeights.pi (fun v => (sources b v).source)).toPMF =
      dependentProductPMF (fun v => (sources b v).source.toPMF) := FiniteProbabilityWeights.toPMF_pi _
  rw [houter]
  simp_rw [hinner]
  have hm := dependentProductPMF_map
    (fun b => dependentProductPMF (fun v => (sources b v).source.toPMF))
    (fun b z v k => (if k = none then c ⟨a,b,v⟩ else 0) + (step ⟨a,b,v⟩ : ℤ) * (z v k : ℤ))
  have hp := congrArg (fun p : PMF (B a → Fin (h a) → Option α → ℤ) =>
    p.map (fun z => shift + ∑ b, fun t : rows => integerBooleanBlockJet (z b) t))
    (containedSupportedProgressionLaw_axis_integer_law B h L H step c hL hH hsubset q r hcell hq a hsize)
  rw [← hm] at hp
  simp only [PMF.map_comp, Function.comp_def] at hp
  exact hp.symm

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedInactiveSource
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

theorem allocatedSupportedSlicedInactiveResidueJetPMF_source
    (hsmall : basisAxisScale (basis j) i ≤ S.value ^ (j.val + 1))
    (hlarge : 2 * inactiveDenominator
      (principalProfileSize (R j) (layerIntegerPrincipalSlots (G := G) B j i).card) ≤ basisAxisScale (basis j) i)
    (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (rows : Finset (Finset α)) (shift : rows → ℤ) :
    let sources := principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r ⟨j,Sum.inr i⟩ hsize
    let lower := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (a : Option α) =>
      if a = none then c ⟨⟨j,Sum.inr i⟩,b,v⟩ else 0
    let strides := fun (b : B ⟨j,Sum.inr i⟩) (v : Fin (j.val + 1)) (_ : Option α) => step ⟨⟨j,Sum.inr i⟩,b,v⟩
    (weightedCubeIntegerSource sources).toPMF.map (affineWeightedCubeIntegerSum sources lower strides rows shift) =
      allocatedSupportedSlicedResidueJetPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows shift := by
  intro sources lower strides
  have hcoeff : (dependentProductPMF (fun a : B ⟨j, Sum.inr i⟩ =>
      allocatedLayerIntegerPMFs B U basis hR hσ S j i
        (principalCoefficientSlot (G := G) (layerSamplerDegree I n) ⟨j, Sum.inr i⟩ a))) =
      PMF.pure (fun _ : B ⟨j, Sum.inr i⟩ => (1 : ℤ)) := by
    ext c
    rw [dependentProductPMF_apply]
    simp_rw [allocatedInactivePrincipalPMF B U basis S j i hR hσ hsmall, inactivePrincipal_large hlarge]
    by_cases hc : c = fun _ => (1 : ℤ)
    · subst c
      simp
    · obtain ⟨a, ha⟩ : ∃ a, c a ≠ 1 := by
        by_contra hn
        apply hc
        funext a
        exact not_not.mp (fun h => hn ⟨a, h⟩)
      rw [PMF.pure_apply_of_ne _ _ hc]
      exact Finset.prod_eq_zero (Finset.mem_univ a) (PMF.pure_apply_of_ne _ _ ha)
  unfold allocatedSupportedSlicedResidueJetPMF
  rw [hcoeff, PMF.pure_bind]
  simp only [one_mul]
  exact containedSupportedProgressionLaw_unit_block_law B (layerSamplerDegree I n)
    (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S)
    hH hsubset q hq r hcell ⟨j,Sum.inr i⟩ hsize rows shift

end Erdos3.VectorPolynomial

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.DenseSliceGridScale
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem dense_slice_product_ratio {n : ℕ} {δ S C M V : ℝ} (H : Fin n → ℝ)
    (hδ : 0 < δ) (hS : 0 < S) (hC : 0 < C) (hM : 0 ≤ M)
    (hH : ∀ j, δ * S ≤ H j)
    (hbase : M / (C * S ^ n) ≤ V) :
    M / (C * ∏ j, H j) ≤ V / δ ^ n := by
  have hp : δ ^ n * S ^ n ≤ ∏ j, H j := by
    simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow] using
      Finset.prod_le_prod (s := Finset.univ) (f := fun _ : Fin n => δ * S) (g := H)
        (fun _ _ => (mul_pos hδ hS).le) (fun j _ => hH j)
  have hd : 0 < δ ^ n * (C * S ^ n) := by positivity
  have hden : δ ^ n * (C * S ^ n) ≤ C * ∏ j, H j := by
    simpa only [mul_left_comm, mul_assoc] using mul_le_mul_of_nonneg_left hp hC.le
  calc
    M / (C * ∏ j, H j) ≤ M / (δ ^ n * (C * S ^ n)) :=
      div_le_div_of_nonneg_left hM hd hden
    _ = (M / (C * S ^ n)) / δ ^ n := by ring
    _ ≤ V / δ ^ n := div_le_div_of_nonneg_right hbase (pow_pos hδ _).le

theorem dense_slice_grid_cardinality {M C S δ : ℝ} (d t : ℕ)
    (hδ : 0 < δ) (hbase : M ^ d ≤ C ^ d * S ^ t) :
    M ^ d ≤ (C ^ d / δ ^ t) * (δ * S) ^ t := by
  calc
    M ^ d ≤ C ^ d * S ^ t := hbase
    _ = _ := by rw [mul_pow]; field_simp

end Erdos3

end

end OAI

end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AllocatedSupportedSlicedInactiveSpectrum
namespace OAI

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
variable {n : Fin m → ℕ} (B : LayerSamplerAxis I n → Type*)
variable [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (basis : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U basis R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "conditioned" => containedSupportedProgressionLaw B (layerSamplerDegree I n)
  (allocatedPrincipalSides B U basis S) H step c (allocatedPrincipalSides_pos B U basis S) hH hsubset q r hcell

variable (hsize : ∀ b v, (Fintype.card α + 1) * q ≤ H ⟨⟨j,Sum.inr i⟩,b,v⟩)

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "side" => inactiveSideLength degree height denom
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "sources" => principalSupportedAxisSources B (layerSamplerDegree I n) H hH q hq r
  (Sigma.mk j (Sum.inr i)) hsize
local notation "lower" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (a : Option α) =>
  ite (a = none) (c (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v))) 0)
local notation "strides" => (fun (b : B (Sigma.mk j (Sum.inr i))) (v : Fin degree) (_ : Option α) =>
  step (Sigma.mk (Sigma.mk j (Sum.inr i)) (Prod.mk b v)))

theorem allocatedSupportedSlicedInactiveGridDensity_approximation
    (hsmall : height ≤ S.value ^ degree) (hlarge : 2 * denom ≤ height)
    {δ : ℝ} (hδ : 0 < δ)
    (hlength : ∀ b v, δ * side ≤ (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    {C ε : ℝ} {M : ℕ} [NeZero M] (hC : 0 ≤ C) (hMK : (M : ℝ) ≤ C * height)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hB : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j, Sum.inr i⟩))
    (hε : 0 < ε) (hε1 : ε ≤ 1) :
    let V := C * cost / δ ^ degree
    let t := degree * rows.card
    let W := (C * cost) ^ rows.card / δ ^ t
    let ζ := uniformBlockRetainedBias j.val rows.card t P V W ε
    let F := uniformBlockSpectrumCover rows M j.val P V (δ * side) ζ
    (F.card : ℝ) ≤ uniformSpectrumSizeConstant j.val rows.card t P V W /
      ε ^ max (majorArcSpectrumExponent j.val rows.card) (majorArcLengthExponent j.val * t) ∧
    (∑ k, ‖∏ b, affineWeightedCubeGridCoefficient (sources b)
      (fun v a => (lower b v a : ℝ)) (strides b) M rows k‖) ≤
        uniformSpectrumAbsoluteCap j.val rows.card t P V W ∧
    ∀ shift z : rows → ℤ,
      ‖(allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z : ℂ) -
        integerGridApproximation (weightedCubeIntegerSource sources)
          (affineWeightedCubeIntegerSum sources lower strides rows shift) height M F z‖ ≤
          ((height : ℝ) / M) ^ rows.card * ε := by
  intro V t W ζ F
  have hside : 0 < side := inactiveSideLength_pos (Nat.zero_lt_succ _) (inactiveDenominator_pos _)
  have hbase : (height : ℝ) ≤ cost * (side : ℝ) ^ degree := by
    exact_mod_cast (inactiveSideLength_lower_power (Nat.zero_lt_succ _) (inactiveDenominator_pos _) hlarge).le
  have hbound : (M : ℝ) ≤ (C * cost) * (side : ℝ) ^ degree :=
    hMK.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbase hC)
  have hratio : (M : ℝ) / (1 * (side : ℝ) ^ degree) ≤ C * cost := by
    rw [one_mul]
    exact (div_le_iff₀ (pow_pos (Nat.cast_pos.mpr hside) _)).mpr hbound
  have hscale (b : B ⟨j,Sum.inr i⟩) : (M : ℝ) / ∏ v, (((sources) b v).length : ℝ) ≤ V := by
    change (M : ℝ) / ∏ v : Fin degree, (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ) ≤ C * cost / δ ^ degree
    simpa only [one_mul, layerSamplerDegree] using dense_slice_product_ratio (n := j.val + 1)
      (fun v => (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ)) hδ (Nat.cast_pos.mpr hside)
      zero_lt_one (Nat.cast_nonneg M) (hlength b) hratio
  have hcard : (M : ℝ) ^ rows.card ≤ W * (δ * side) ^ t := by
    apply dense_slice_grid_cardinality rows.card t hδ
    simpa only [mul_pow, ← pow_mul] using pow_le_pow_left₀ (Nat.cast_nonneg M) hbound rows.card
  have hV : 0 ≤ V := by dsimp [V]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hL : 0 ≤ δ * side := mul_nonneg hδ.le (Nat.cast_nonneg _)
  have hs (b : B ⟨j,Sum.inr i⟩) (v : Fin degree) :=
    (principalSupportedAxisSources_primitive B (layerSamplerDegree I n) H hH q hq r
      ⟨j,Sum.inr i⟩ hsize b v A).mono hsP
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Fintype.card_coe] using uniformBlockSpectrumCover_polynomial_card rows M j.val t
      hP hV hW hL hε hε1 (by simpa only [Fintype.card_coe] using hcard)
  · exact (affine_weightedCube_uniform_spectrum sources (fun b v a => (lower b v a : ℝ)) strides
      A hA hP hV hW hL hε hs hlength (fun b v _ => hstep b v) (fun b v _ => hstride b v)
      M t (Nat.pos_of_ne_zero (NeZero.ne M)) rows hrows hB hcard hscale).2
  · intro shift z
    have he := affine_weightedCube_grid_density sources lower strides A hA hP hV hW hL hε hs hlength
      (fun b v _ => hstep b v) (fun b v _ => hstride b v) height M t rows hrows hB hcard hscale shift z
    have hlaw := allocatedSupportedSlicedInactiveResidueJetPMF_source B U basis hR hσ S q hq r H step c
      hH hsubset hcell j i hsmall hlarge hsize rows shift
    have hd := integerGridDensity_eq_of_pmf_image (weightedCubeIntegerSource sources)
      (affineWeightedCubeIntegerSum sources lower strides rows shift) _ hlaw height M z
    have hd' : integerGridDensity (weightedCubeIntegerSource sources)
        (affineWeightedCubeIntegerSum sources lower strides rows shift) height M z =
        allocatedSupportedSlicedGridDensity B U basis hR hσ S q r H step c hH hsubset hcell j i M rows shift z := by
      simpa only [allocatedSupportedSlicedGridDensity, Fintype.card_coe] using hd
    rw [← hd']
    exact he

end Erdos3.VectorPolynomial

end

end OAI

end

theorem solution.{u_1, u_2, u_3, u_4, u_5} : type_of% @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveGridDensity_approximation.{u_1, u_2, u_3, u_4, u_5} := @OAI.Erdos3.VectorPolynomial.allocatedSupportedSlicedInactiveGridDensity_approximation.{u_1, u_2, u_3, u_4, u_5}
