-- Prove2me | solution 1 for OAI.Erdos3.weightedPositiveAffineModerateGridCoefficient_minor_polynomial_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-17T11:29:01.533904+00:00
-- url     : https://prove2.me/submissions/15f2e3a0-3a9d-432f-b1a8-b785935ba5ca

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B150
import Theorems.Thm_OAI_Erdos3_affine_weightedModerateBlock_major_arc_s2
import Theorems.Thm_OAI_Erdos3_polynomial_affine_weightedCubeBlock_major_arc_s2

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.EmbeddedFiniteConditioning
namespace OAI

section

namespace Erdos3.FiniteProbabilityWeights

open scoped BigOperators

theorem exists_positive_weight_norm_ge_mean {X : Type*} [Fintype X]
    (p : FiniteProbabilityWeights X) (f : X → ℂ) :
    ∃ x, 0 < p.weight x ∧ ‖p.complexMean f‖ ≤ ‖f x‖ := by
  classical
  let A := Finset.univ.filter (fun x => 0 < p.weight x)
  have hA : A.Nonempty := by
    by_contra hn
    have hzero (x : X) : p.weight x = 0 := by
      apply le_antisymm _ (p.nonneg x)
      apply le_of_not_gt
      intro hx
      exact hn ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    have ht := p.total
    simp only [hzero, Finset.sum_const_zero] at ht
    norm_num at ht
  obtain ⟨x, hx, hmax⟩ := A.exists_max_image (fun y => ‖f y‖) hA
  refine ⟨x, (Finset.mem_filter.mp hx).2, ?_⟩
  apply (norm_sum_le _ _).trans
  calc
    (∑ y, ‖(p.weight y : ℂ) * f y‖) = ∑ y, p.weight y * ‖f y‖ := by
      apply Finset.sum_congr rfl
      intro y _
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (p.nonneg y)]
    _ ≤ ∑ y, p.weight y * ‖f x‖ := by
      apply Finset.sum_le_sum
      intro y _
      by_cases hy : 0 < p.weight y
      · exact mul_le_mul_of_nonneg_left (hmax y (Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩)) hy.le
      · have hz : p.weight y = 0 := le_antisymm (le_of_not_gt hy) (p.nonneg y)
        simp only [hz, zero_mul, le_refl]
    _ = ‖f x‖ := by rw [← Finset.sum_mul, p.total, one_mul]

end Erdos3.FiniteProbabilityWeights

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.LocalizationPolynomialScales
namespace OAI

section

namespace Erdos3

theorem localizationRadius_le_one {U ε : ℝ} (hU : 1 ≤ U) (hε1 : ε ≤ 1) :
    localizationRadius U ε ≤ 1 := by
  have hp : 1 ≤ U ^ 2 := one_le_pow₀ hU
  unfold localizationRadius
  apply (div_le_one (by positivity)).mpr
  linarith

theorem localizationRadius_scale {U ε : ℝ} (hU : 1 ≤ U) :
    U ^ 2 * localizationRadius U ε = ε / 8 := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationRadius
  field_simp

theorem localizationMesh_scale {U ε : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    (2 * U ^ 3 / localizationRadius U ε) * localizationMesh U ε = ε / 8 := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationRadius localizationMesh
  field_simp
  ring

theorem localizationRadius_length {U ε W : ℝ} (hU : 1 ≤ U) (hε : 0 < ε) :
    localizationRadius U ε * localizationLengthBudget U ε W * ε = 32 * U ^ 4 * W := by
  have hU0 : U ≠ 0 := by linarith
  unfold localizationRadius localizationLengthBudget
  field_simp
  ring

theorem localization_inverse_length_error {U ε W L : ℝ}
    (hU : 1 ≤ U) (hε : 0 < ε) (hW : 1 ≤ W) (hL : 0 < L)
    (hlen : localizationLengthBudget U ε W ≤ L) :
    2 * U ^ 3 / (localizationRadius U ε * L) ≤ ε / 4 := by
  have hr := localizationRadius_pos hU hε
  have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlen hr.le) hε.le
  rw [localizationRadius_length hU hε] at hmul
  have hp : U ^ 3 ≤ U ^ 4 := pow_le_pow_right₀ hU (by decide : 3 ≤ 4)
  have hprod : U ^ 4 ≤ U ^ 4 * W := le_mul_of_one_le_right (by positivity) hW
  have hp0 : 0 ≤ U ^ 3 := by positivity
  apply (div_le_iff₀ (mul_pos hr hL)).mpr
  nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.GeometricLocalizationThreshold
namespace OAI

section

namespace Erdos3

theorem localizationThreshold_step {U ζ : ℝ} (hU : 1 ≤ U) (hζ : 0 < ζ)
    {i m : ℕ} (hi : i + 1 ≤ m) :
    localizationThreshold U ζ m + U ^ 2 * localizationThreshold U ζ (i + 1) ≤
      localizationThreshold U ζ i := by
  have hε := localizationThreshold_antitone hU hζ.le hi
  have hη := localizationThreshold_pos hU hζ (i + 1)
  have hp : 1 ≤ U ^ 2 := one_le_pow₀ hU
  have he : localizationThreshold U ζ i =
      2 * U ^ 2 * localizationThreshold U ζ (i + 1) := by
    have hC : 2 * U ^ 2 ≠ 0 := by positivity
    unfold localizationThreshold
    rw [pow_succ]
    field_simp
    exact pow_succ' _ _
  rw [he]
  nlinarith

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

theorem positiveModerateLengthBudget_bounds (n : ℕ) {U ζ : ℝ}
    (hU : 1 ≤ U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    majorArcLengthConstant n U / ζ ^ majorArcLengthExponent n ≤
      positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n ∧
    majorArcLengthConstant (n + 1) U / ζ ^ majorArcLengthExponent (n + 1) ≤
      positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n := by
  have h0 := majorArcLengthConstant_pos n hU
  have h1 := majorArcLengthConstant_pos (n + 1) hU
  have hC := (positiveModerateLengthConstant_pos n hU).le
  constructor
  · exact inverse_power_mono hC (by unfold positiveModerateLengthConstant; linarith)
      hζ hζ1 (by unfold positiveModerateLengthExponent; omega)
  · exact inverse_power_mono hC (by unfold positiveModerateLengthConstant; linarith)
      hζ hζ1 (by unfold positiveModerateLengthExponent; omega)

theorem positiveModerateCoverConstant_one_le (n j : ℕ) {U V : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) : 1 ≤ positiveModerateCoverConstant n j U V := by
  have hL := majorArcLengthConstant_pos (n + 1) hU
  have hS := majorArcCoverConstant_one_le n j hU (show 0 ≤ 4 * V by positivity)
  have hT := majorArcCoverConstant_one_le (n + 1) j hU hV
  unfold positiveModerateCoverConstant
  nlinarith

theorem positiveModerateCoverBudget_bounds (n j : ℕ) {U V ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    majorArcCoverConstant n j U (4 * V) / ζ ^ majorArcCoverExponent n j ≤
      positiveModerateCoverConstant n j U V / ζ ^ positiveModerateCoverExponent n j ∧
    majorArcCoverConstant (n + 1) j U V / ζ ^ majorArcCoverExponent (n + 1) j ≤
      positiveModerateCoverConstant n j U V / ζ ^ positiveModerateCoverExponent n j ∧
    (majorArcLengthConstant (n + 1) U / ζ ^ majorArcLengthExponent (n + 1)) *
        (majorArcCoverConstant n j U (4 * V) / ζ ^ majorArcCoverExponent n j) ≤
      positiveModerateCoverConstant n j U V / ζ ^ positiveModerateCoverExponent n j := by
  have hL := majorArcLengthConstant_pos (n + 1) hU
  have hS := majorArcCoverConstant_one_le n j hU (show 0 ≤ 4 * V by positivity)
  have hT := majorArcCoverConstant_one_le (n + 1) j hU hV
  have hC := (show (0 : ℝ) ≤ 1 by norm_num).trans
    (positiveModerateCoverConstant_one_le n j hU hV)
  refine ⟨?_, ?_, ?_⟩
  · exact inverse_power_mono hC (by unfold positiveModerateCoverConstant; nlinarith)
      hζ hζ1 (by unfold positiveModerateCoverExponent; omega)
  · exact inverse_power_mono hC (by unfold positiveModerateCoverConstant; nlinarith)
      hζ hζ1 (by unfold positiveModerateCoverExponent; omega)
  · rw [div_mul_div_comm, ← pow_add]
    exact inverse_power_mono hC (by unfold positiveModerateCoverConstant; nlinarith)
      hζ hζ1 (by unfold positiveModerateCoverExponent; omega)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Probability.ScalarCubeBoundaryMass
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators

theorem scalarCubeBoundaryConstant_pos (α : Type*) [Fintype α] [DecidableEq α] :
    0 < scalarCubeBoundaryConstant α := by
  have h := scalarCubeDomainDensity_pos α
  unfold scalarCubeBoundaryConstant
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ScalarResidueInteriorCell
namespace OAI

section

namespace Erdos3

theorem residueCellLength_bounds {δ : ℝ} {L M : ℕ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hL : 0 < L) (hM : 0 < M)
    (hlarge : 2 * (M : ℝ) ≤ δ * L) :
    0 < residueCellLength δ L M ∧ residueCellLength δ L M ≤ L ∧
      δ * L / (2 * M) ≤ (residueCellLength δ L M : ℝ) ∧
      (M : ℝ) / L * residueCellLength δ L M ≤ δ := by
  have hL' : (0 : ℝ) < L := by exact_mod_cast hL
  have hM' : (0 : ℝ) < M := by exact_mod_cast hM
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hx0 : 0 ≤ δ * L / M := by positivity
  have hx2 : 2 ≤ δ * L / M := (le_div_iff₀ hM').mpr hlarge
  have hfloor := Nat.floor_le hx0
  have hceil := Nat.lt_floor_add_one (δ * L / M)
  have hpos : 0 < residueCellLength δ L M := by
    unfold residueCellLength
    apply Nat.floor_pos.mpr
    linarith
  have hxL : δ * L / M ≤ L := by
    apply (div_le_iff₀ hM').mpr
    nlinarith
  have hNL : residueCellLength δ L M ≤ L := by
    exact_mod_cast hfloor.trans hxL
  refine ⟨hpos, hNL, ?_, ?_⟩
  · change δ * L / (2 * M) ≤ (⌊δ * L / M⌋₊ : ℝ)
    have he : δ * L / (2 * M) = (δ * L / M) / 2 := by ring
    rw [he]
    have hp : (1 : ℝ) ≤ ⌊δ * L / M⌋₊ := by exact_mod_cast hpos
    linarith
  · have hmul := (le_div_iff₀ hM').mp hfloor
    change (M : ℝ) / L * (⌊δ * L / M⌋₊ : ℝ) ≤ δ
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hL').mpr
    nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.ScalarCubeProductRiemannBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeGridBoundaryConstant_pos (I : Type*) [Fintype I] :
    0 < scalarCubeGridBoundaryConstant I := by
  unfold scalarCubeGridBoundaryConstant
  simp only [Fintype.card_prod, Fintype.card_bool, Fintype.card_finset]
  positivity

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoarseLocalizationError
namespace OAI

section

namespace Erdos3

theorem coarse_localization_error {U B C D H T M r δ L η : ℝ}
    (hU : 1 ≤ U) (hB0 : 0 ≤ B) (_hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hH0 : 0 ≤ H) (hT0 : 0 ≤ T) (hM0 : 0 ≤ M)
    (hB : B ≤ U) (hC : C ≤ U) (hD : D ≤ U) (hH : H ≤ U) (hT : T ≤ U) (hM : M ≤ U)
    (hr : 0 < r) (hr1 : r ≤ 1) (hδ : 0 ≤ δ) (hL : 0 < L) (hη : 0 ≤ η)
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ U) :
    B * (A * r + (D + H / r) * (M / L)) + C * ((T + B * H / r) * δ + B * η) ≤
      U ^ 2 * r + 2 * U ^ 3 / (r * L) + (2 * U ^ 3 / r) * δ + U ^ 2 * η := by
  have hU0 : 0 < U := by linarith
  have hsum : D + H / r ≤ 2 * U / r := by
    apply (le_div_iff₀ hr).mpr
    have hDr : D * r ≤ U := (mul_le_mul_of_nonneg_right hD hr.le).trans
      (mul_le_of_le_one_right hU0.le hr1)
    have he : (D + H / r) * r = D * r + H := by field_simp
    rw [he]
    linarith
  have hsum' : T + B * H / r ≤ 2 * U ^ 2 / r := by
    apply (le_div_iff₀ hr).mpr
    have hTr : T * r ≤ U := (mul_le_mul_of_nonneg_right hT hr.le).trans
      (mul_le_of_le_one_right hU0.le hr1)
    have hBH : B * H ≤ U ^ 2 := by nlinarith [mul_le_mul hB hH hH0 hU0.le]
    have he : (T + B * H / r) * r = T * r + B * H := by field_simp
    rw [he]
    nlinarith
  calc
    _ ≤ U * (U * r + (2 * U / r) * (U / L)) + U * ((2 * U ^ 2 / r) * δ + U * η) := by
      gcongr
    _ = _ := by field_simp; ring

theorem polynomial_localization_error {U B C D H T M L η ε W : ℝ}
    (hU : 1 ≤ U) (hB0 : 0 ≤ B) (hC0 : 0 ≤ C) (hD0 : 0 ≤ D)
    (hH0 : 0 ≤ H) (hT0 : 0 ≤ T) (hM0 : 0 ≤ M)
    (hB : B ≤ U) (hC : C ≤ U) (hD : D ≤ U) (hH : H ≤ U) (hT : T ≤ U) (hM : M ≤ U)
    (hL : 0 < L) (hη : 0 ≤ η) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W)
    (hlen : localizationLengthBudget U ε W ≤ L) {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ U) :
    B * (A * localizationRadius U ε + (D + H / localizationRadius U ε) * (M / L)) +
      C * ((T + B * H / localizationRadius U ε) * localizationMesh U ε + B * η) ≤ ε + U ^ 2 * η := by
  have hc := coarse_localization_error hU hB0 hC0 hD0 hH0 hT0 hM0 hB hC hD hH hT hM
    (localizationRadius_pos hU hε) (localizationRadius_le_one hU hε1)
    (localizationMesh_pos hU hε).le hL hη hA0 hA
  rw [localizationRadius_scale hU, localizationMesh_scale hU hε] at hc
  have hi := localization_inverse_length_error hU hε hW hL hlen
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientSliceEmbedding
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped BigOperators NNReal

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

theorem cellLength_pos : 0 < d.cellLength :=
  (residueCellLength_bounds d.mesh_pos d.mesh_le_one d.length_pos
    ((d.modulus_pos none).trans_le (d.modulus_le none)) d.meshLarge).1

theorem cellLength_lower : d.mesh * d.length / (2 * d.modulusBound) ≤ (d.cellLength : ℝ) :=
  (residueCellLength_bounds d.mesh_pos d.mesh_le_one d.length_pos
    ((d.modulus_pos none).trans_le (d.modulus_le none)) d.meshLarge).2.2.1

end ScalarCubeLocalizationData

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

namespace ScalarCubeLocalizationData

variable {I : Type*} [Fintype I] [DecidableEq I] (d : ScalarCubeLocalizationData I)

theorem length_le_lengthLoss_mul_cellLength :
    (d.length : ℝ) ≤ d.lengthLoss * d.cellLength := by
  have hM : (0 : ℝ) < d.modulusBound := by
    exact_mod_cast (d.modulus_pos none).trans_le (d.modulus_le none)
  have h := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * d.modulusBound)).mp d.cellLength_lower
  unfold lengthLoss
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ d.mesh_pos).mpr
  nlinarith

end ScalarCubeLocalizationData

theorem reciprocal_product_le_of_lengths {J : Type*} [Fintype J]
    (a b c : J → ℝ) (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hlen : ∀ j, a j ≤ c j * b j) {Q : ℝ} (hQ : 0 ≤ Q) :
    Q / (∏ j, b j) ≤ Q * (∏ j, c j) / (∏ j, a j) := by
  have hprod := Finset.prod_le_prod (s := Finset.univ) (fun j _ => (ha j).le) (fun j _ => hlen j)
  rw [Finset.prod_mul_distrib] at hprod
  apply (div_le_div_iff₀ (Finset.prod_pos (fun j _ => hb j)) (Finset.prod_pos (fun j _ => ha j))).mpr
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hprod hQ

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.CoefficientLengthProduct
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem coefficient_inverse_product_le {n : ℕ} {a₀ b₀ κ C Q : ℝ}
    (a b : Fin n → ℝ) (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) (hκ : 0 < κ)
    (ha : ∀ j, 0 < a j) (hb : ∀ j, 0 < b j)
    (hlen₀ : a₀ ≤ C * b₀) (hlen : ∀ j, a j ≤ C * b j) (hQ : 0 ≤ Q) :
    Q / ((κ * b₀) * ∏ j, b j) ≤ Q * C ^ (n + 1) / ((κ * a₀) * ∏ j, a j) := by
  have hp := reciprocal_product_le_of_lengths (Fin.cons a₀ a) (Fin.cons b₀ b)
    (fun _ : Fin (n + 1) => C)
    (Fin.cases ha₀ ha) (Fin.cases hb₀ hb) (Fin.cases hlen₀ hlen) hQ
  simp only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin] at hp
  calc
    _ = (Q / (b₀ * ∏ j, b j)) / κ := by ring
    _ ≤ (Q * C ^ (n + 1) / (a₀ * ∏ j, a j)) / κ :=
      div_le_div_of_nonneg_right hp hκ.le
    _ = _ := by ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueCutoffLengthBudget
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

theorem scalarCubeCutoffLipschitzConstant_eq (I : Type*) [Fintype I] (A r : ℝ≥0) :
    (scalarCubeCutoffLipschitzConstant I A r : ℝ) =
      scalarCubeCutoffDerivativeNumerator I A / r := by
  simp only [scalarCubeCutoffLipschitzConstant, scalarCubeCutoffDerivativeNumerator,
    NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_add, NNReal.coe_one]
  ring

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.PolynomialScalarCubeLength
namespace OAI

section

namespace Erdos3

open MeasureTheory
open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ε W : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hε : 0 < ε) (hε1 : ε ≤ 1) (hW : 1 ≤ W)
    (hlen : localizationLengthBudget U ε W ≤ s.length)

theorem polynomialLocalizationData_cellLength :
    W ≤ ((s.polynomialLocalizationData A hA h hε hε1 hW hlen).cellLength : ℝ) := by
  let d := s.polynomialLocalizationData A hA h hε hε1 hW hlen
  have hM : (0 : ℝ) < s.modulusBound := by
    exact_mod_cast (s.modulus_pos none).trans_le (s.modulus_le none)
  have hδ := localizationMesh_pos h.one_le hε
  have hδL : 2 * U * W ≤ localizationMesh U ε * s.length := by
    simpa only [localizationMesh_length h.one_le hε] using mul_le_mul_of_nonneg_left hlen hδ.le
  apply le_trans _ d.cellLength_lower
  change W ≤ localizationMesh U ε * s.length / (2 * s.modulusBound)
  apply (le_div_iff₀ (by positivity)).mpr
  have hm := mul_le_mul_of_nonneg_right h.modulus_le (by linarith : 0 ≤ W)
  nlinarith

theorem polynomialLocalizationData_error {η : ℝ} (hη : 0 ≤ η) :
    (s.polynomialLocalizationData A hA h hε hε1 hW hlen).error η ≤ ε + U ^ 2 * η := by
  have hM : 0 < s.modulusBound := (s.modulus_pos none).trans_le (s.modulus_le none)
  have hC0 : 0 ≤ paddedResidueDensityCap I s.modulusBound := by
    have hc := scalarCubeResidueDensityCap_pos I s.modulusBound hM
    unfold paddedResidueDensityCap
    positivity
  have hG0 : 0 ≤ 2 * scalarCubeGridBoundaryConstant I / volume.real (scalarCubeDomain I) := by
    have hg := scalarCubeGridBoundaryConstant_pos I
    have hv := scalarCubeDomain_volumeReal_pos I
    positivity
  have hH0 : 0 ≤ scalarCubeCutoffDerivativeNumerator I A := by
    unfold scalarCubeCutoffDerivativeNumerator
    positivity
  have he := polynomial_localization_error h.one_le s.weightBound.coe_nonneg hC0 hG0 hH0
    s.weightLipschitz.coe_nonneg (Nat.cast_nonneg s.modulusBound)
    h.weight_le h.density_le h.grid_le h.derivative_le h.weightLipschitz_le h.modulus_le
    (by exact_mod_cast s.length_pos) hη hε hε1 hW hlen
    (scalarCubeBoundaryConstant_pos I).le h.boundary_le
  let r : ℝ≥0 := ⟨localizationRadius U ε, (localizationRadius_pos h.one_le hε).le⟩
  have hr : (r : ℝ) = localizationRadius U ε := rfl
  have hq : (scalarCubeCutoffLipschitzConstant I A r : ℝ) =
      scalarCubeCutoffDerivativeNumerator I A / localizationRadius U ε :=
    scalarCubeCutoffLipschitzConstant_eq I A r
  change (s.weightBound : ℝ) * scalarCubeResidueCutoffBudget I A r s.length s.modulusBound +
    paddedResidueDensityCap I s.modulusBound *
      (((s.weightLipschitz : ℝ) + s.weightBound * scalarCubeCutoffLipschitzConstant I A r) *
        localizationMesh U ε + s.weightBound * η) ≤ _
  unfold scalarCubeResidueCutoffBudget
  rw [hq, hr]
  simpa only [mul_div_assoc] using he

end NormalizedScalarCubeSource

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal

namespace NormalizedScalarCubeSource

theorem polynomialLocalizationData_lengthLoss {I : Type*} [Fintype I] [DecidableEq I]
    (s : NormalizedScalarCubeSource I) (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition)
    {U ε W : ℝ} (h : ScalarCubePrimitiveBudget s A U) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hW : 1 ≤ W) (hlen : localizationLengthBudget U ε W ≤ s.length) :
    (s.polynomialLocalizationData A hA h hε hε1 hW hlen).lengthLoss ≤
      localizationLengthBudget U ε 1 := by
  change 2 * (s.modulusBound : ℝ) / localizationMesh U ε ≤ _
  calc
    _ ≤ 2 * U / localizationMesh U ε :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h.modulus_le (by norm_num))
        (localizationMesh_pos h.one_le hε).le
    _ = _ := by
      have hU : U ≠ 0 := ne_of_gt (by linarith [h.one_le])
      unfold localizationMesh localizationLengthBudget
      field_simp
      ring

end NormalizedScalarCubeSource

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.PolynomialWeightedCubeMajorArc
namespace OAI

section

namespace Erdos3

open scoped NNReal

namespace NormalizedScalarCubeSource

variable {I : Type*} [Fintype I] [DecidableEq I] (s : NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {n : ℕ} {U ζ : ℝ}
    (h : ScalarCubePrimitiveBudget s A U) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : localizedMajorArcLengthBudget n U ζ ≤ s.length)

theorem majorArcLocalizationData_cellLength :
    localizedMajorArcBudget n U ζ ≤
      ((s.majorArcLocalizationData A hA h hζ hζ1 hlen).cellLength : ℝ) := by
  exact (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
    (s.polynomialLocalizationData_cellLength A hA h
      (localizationThreshold_pos h.one_le hζ (n + 1))
      (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
      (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen)

theorem majorArcLocalizationData_error {i : ℕ} (hi : i + 1 ≤ n + 1) :
    (s.majorArcLocalizationData A hA h hζ hζ1 hlen).error (localizationThreshold U ζ (i + 1)) ≤
      localizationThreshold U ζ i := by
  exact (s.polynomialLocalizationData_error A hA h
    (localizationThreshold_pos h.one_le hζ (n + 1))
    (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen
    (localizationThreshold_pos h.one_le hζ (i + 1)).le).trans
      (localizationThreshold_step h.one_le hζ hi)

theorem majorArcLocalizationData_lengthLoss :
    (s.majorArcLocalizationData A hA h hζ hζ1 hlen).lengthLoss ≤
      localizationLengthBudget U (localizationThreshold U ζ (n + 1)) 1 :=
  s.polynomialLocalizationData_lengthLoss A hA h
    (localizationThreshold_pos h.one_le hζ (n + 1))
    (localizationThreshold_le_one h.one_le hζ hζ1 (n + 1))
    (by linarith [localizedMajorArcBudget_pos n h.one_le hζ]) hlen

end NormalizedScalarCubeSource
end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal
open CircleFourier

theorem polynomial_affine_weightedModerateBlock_major_arc {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : localizedMajorArcLengthBudget n U ζ ≤ c.length)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (shift : ℝ) (t : ℕ) (ht : 0 < t)
    (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hbias : ζ ≤ ‖c.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
        (fun x => character (((shift + (t : ℝ) * (z none : ℝ)) *
          booleanBlockPhase ξ (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ (localizedMajorArcBudget n U ζ * (((t * c.modulus none : ℕ) : ℝ) * U ^ n)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ /
          ((((t * c.modulus none : ℕ) : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) := by
  let d j := (s j).majorArcLocalizationData A hA (h j) hζ hζ1 (hlen j)
  let e := c.majorArcLocalizationData A hA hc hζ hζ1 hclen
  let τ : Fin (n + 2) → ℝ := fun i => localizationThreshold U ζ i.val
  have hτ (j : Fin (n + 1)) : 0 < τ j.succ := localizationThreshold_pos hc.one_le hζ _
  have he : e.error (τ 1) ≤ τ 0 := by
    simpa only [τ, Fin.val_one, Fin.val_zero] using
      c.majorArcLocalizationData_error A hA hc hζ hζ1 hclen (i := 0) (by omega)
  have hd (j : Fin n) : (d j).error (τ j.succ.succ) ≤ τ j.castSucc.succ :=
    (s j).majorArcLocalizationData_error A hA (h j) hζ hζ1 (hlen j) (by omega)
  have hR (j : Fin n) (i : Option I) : ((v j i * (d j).modulus i : ℕ) : ℝ) ≤ U :=
    hstride j i
  have hN (j : Fin n) : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ (d j).cellLength :=
    (s j).majorArcLocalizationData_cellLength A hA (h j) hζ hζ1 (hlen j)
  have hM : multiaffineBiasBudget n (τ (Fin.last (n + 1))) ≤ e.cellLength :=
    c.majorArcLocalizationData_cellLength A hA hc hζ hζ1 hclen
  have hb : τ 0 ≤ ‖e.source.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (d j).source)).complexMean
        (fun x => character (((shift + (t : ℝ) * (z none : ℝ)) *
          booleanBlockPhase ξ (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))‖ := by
    change localizationThreshold U ζ 0 ≤ _
    rw [localizationThreshold_zero]
    exact hbias
  obtain ⟨D, hD, hDb, a, ha⟩ := affine_weightedModerateBlock_major_arc_s2 e d τ hτ he hd shift t ht u v hv ξ J hJ hR hN hM hb
  refine ⟨D, hD, hDb, a, fun S => (ha S).trans ?_⟩
  have hcloss := c.majorArcLocalizationData_lengthLoss A hA hc hζ hζ1 hclen
  have hsloss j := (s j).majorArcLocalizationData_lengthLoss A hA (h j) hζ hζ1 (hlen j)
  apply coefficient_inverse_product_le (fun j => ((s j).length : ℝ))
    (fun j => ((d j).cellLength : ℝ))
    (by exact_mod_cast c.length_pos) (by exact_mod_cast e.cellLength_pos)
    (by exact_mod_cast Nat.mul_pos ht (c.modulus_pos none))
    (fun j => by exact_mod_cast (s j).length_pos)
    (fun j => by exact_mod_cast (d j).cellLength_pos)
    (e.length_le_lengthLoss_mul_cellLength.trans
      (mul_le_mul_of_nonneg_right hcloss (Nat.cast_nonneg _)))
    (fun j => (d j).length_le_lengthLoss_mul_cellLength.trans
      (mul_le_mul_of_nonneg_right (hsloss j) (Nat.cast_nonneg _)))
    (localizedMajorArcBudget_pos n hc.one_le hζ).le

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.AffineShortCoefficientMajorArc
namespace OAI

section

namespace Erdos3

open scoped BigOperators Classical NNReal
open CircleFourier

theorem booleanBlockPhase_frequency_mul {G I : Type*} [Fintype G] [Fintype I] [DecidableEq I]
    (a : ℝ) (ξ : Finset I → ℝ) (x : G → Option I → ℝ) :
    booleanBlockPhase (fun S => a * ξ S) x = a * booleanBlockPhase ξ x := by
  simp only [booleanBlockPhase, Finset.mul_sum, mul_assoc]

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical NNReal
open CircleFourier

theorem affine_weighted_positiveCoefficient_major_arc {Ω I : Type*} [Fintype Ω]
    [Fintype I] [DecidableEq I] {n : ℕ}
    (p : FiniteProbabilityWeights Ω) (coefficient : Ω → ℤ)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ a₀ T : ℝ}
    (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (ha₀ : 0 < a₀)
    (hcoefficient : ∀ z, p.weight z ≠ 0 → a₀ ≤ (coefficient z : ℝ) ∧ (coefficient z : ℝ) ≤ T)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (ξ : Finset I → ℝ) (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (hbias : ζ ≤ ‖p.complexMean (fun z =>
      (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
        (fun x => character (((coefficient z : ℝ) *
          booleanBlockPhase ξ (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))‖) :
    ∃ D : ℕ, 0 < D ∧
      (D : ℝ) ≤ T * (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card ∧
      ∃ a : J → ℤ, ∀ S : J, |ξ S - (a S : ℝ) / D| ≤
        localizedMajorArcErrorBudget n U ζ / (a₀ * ∏ j, ((s j).length : ℝ)) := by
  obtain ⟨z, hz, hnorm⟩ := p.exists_positive_weight_norm_ge_mean (fun z =>
    (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character (((coefficient z : ℝ) *
        booleanBlockPhase ξ (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle)))
  have hcz := hcoefficient z hz.ne'
  have hcpos : 0 < (coefficient z : ℝ) := ha₀.trans_le hcz.1
  have hczpos : 0 < coefficient z := by exact_mod_cast hcpos
  let c : ℕ := (coefficient z).toNat
  have hcZ : (c : ℤ) = coefficient z := Int.toNat_of_nonneg hczpos.le
  have hcR : (c : ℝ) = (coefficient z : ℝ) := by exact_mod_cast hcZ
  have hc : 0 < c := Nat.cast_pos.mp (by rw [hcR]; exact hcpos)
  have hscaled : ζ ≤ ‖(FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
      (fun x => character ((booleanBlockPhase (fun S => (coefficient z : ℝ) * ξ S)
        (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) : CircleFourier.Circle))‖ := by
    simpa only [booleanBlockPhase_frequency_mul] using hbias.trans hnorm
  obtain ⟨D, hD, hDb, a, happ⟩ := polynomial_affine_weightedCubeBlock_major_arc_s2 s A hA h hζ hζ1 hlen u v hv hstride
    (fun S => (coefficient z : ℝ) * ξ S) J hJ hscaled
  have hbound : 0 ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card :=
    (Nat.cast_nonneg D).trans hDb
  refine ⟨c * D, Nat.mul_pos hc hD, ?_, a, ?_⟩
  · rw [Nat.cast_mul, hcR]
    exact (mul_le_mul_of_nonneg_left hDb hcpos.le).trans
      (mul_le_mul_of_nonneg_right hcz.2 hbound)
  · intro S
    rw [Nat.cast_mul, hcR]
    have heq : (coefficient z : ℝ) * (ξ S - (a S : ℝ) / ((coefficient z : ℝ) * D)) =
        (coefficient z : ℝ) * ξ S - (a S : ℝ) / D := by
      field_simp [hcpos.ne', (Nat.cast_pos.mpr hD : (0 : ℝ) < D).ne']
    have hmul : (coefficient z : ℝ) * |ξ S - (a S : ℝ) / ((coefficient z : ℝ) * D)| ≤
        localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ) := by
      calc
        _ = |(coefficient z : ℝ) * (ξ S - (a S : ℝ) / ((coefficient z : ℝ) * D))| := by
          rw [abs_mul, abs_of_pos hcpos]
        _ = _ := congrArg abs heq
        _ ≤ _ := happ S
    calc
      _ ≤ (localizedMajorArcErrorBudget n U ζ / ∏ j, ((s j).length : ℝ)) / a₀ :=
        (le_div_iff₀ ha₀).mpr ((mul_comm _ _).trans_le
          ((mul_le_mul_of_nonneg_right hcz.1 (abs_nonneg _)).trans hmul))
      _ = _ := by ring

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

open scoped BigOperators NNReal Classical
open CircleFourier

theorem weightedAffineModerateGridCoefficient_mem_major {n : ℕ} {I : Type*} [Fintype I] [DecidableEq I]
    (c : NormalizedScalarCubeSource Empty) (s : Fin n → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hclen : localizedMajorArcLengthBudget n U ζ ≤ c.length)
    (hlen : ∀ j, localizedMajorArcLengthBudget n U ζ ≤ (s j).length)
    (u : Fin n → Option I → ℝ) (v : Fin n → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (shift : ℝ) {M Q H : ℕ} (hM : 0 < M)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n)
    (hQ : (localizedMajorArcBudget n U ζ * ((c.modulus none : ℝ) * U ^ n)) ^ J.card ≤ Q)
    (hH : M * (localizedMajorArcErrorBudget n U ζ /
      (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ))) ≤ H)
    (k : J → Fin M) (hk : ζ ≤ ‖weightedAffineModerateGridCoefficient c s u v shift M J k‖) :
    k ∈ rationalGridMajorBox J M Q H := by
  obtain ⟨D, hD, hDQ, a, ha⟩ := polynomial_affine_weightedModerateBlock_major_arc c s A hA hc h hζ hζ1
    hclen hlen shift 1 Nat.zero_lt_one u v hv hstride (gridJetFrequency M J k) J hJ (by
      simpa only [weightedAffineModerateGridCoefficient, Nat.cast_one, one_mul] using hk)
  simp only [one_mul] at hDQ ha
  apply mem_rationalGridMajorBox hM k hD (by exact_mod_cast hDQ.trans hQ) a _ hH
  intro S
  simpa only [gridJetFrequency_apply, one_mul] using ha S

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators NNReal Classical

theorem weightedPositiveAffineModerateGridCoefficient_mem_polynomial {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : NormalizedScalarCubeSource Empty)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n ≤
      (s j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : ζ ≤ ‖weightedAffineModerateGridCoefficient c s u v 0 M J k‖) :
    k ∈ polynomialGridCover J M (positiveModerateCoverConstant n J.card U V)
      (positiveModerateCoverExponent n J.card) ζ := by
  have hU := hc.one_le
  have hU0 : 0 ≤ U := (by norm_num : (0 : ℝ) ≤ 1).trans hU
  have hLc : 0 < (c.length : ℝ) := Nat.cast_pos.mpr c.length_pos
  have hP : 0 < ∏ j, ((s j).length : ℝ) :=
    Finset.prod_pos (fun j _ => Nat.cast_pos.mpr (s j).length_pos)
  have hlength := positiveModerateLengthBudget_bounds n hU hζ hζ1
  have hcover := positiveModerateCoverBudget_bounds n J.card hU hV hζ hζ1
  by_cases hlong : majorArcLengthConstant (n + 1) U / ζ ^ majorArcLengthExponent (n + 1) ≤
      (c.length : ℝ)
  · have hm : (c.modulus none : ℝ) ≤ U :=
      (by exact_mod_cast c.modulus_le none : (c.modulus none : ℝ) ≤ c.modulusBound).trans
        hc.modulus_le
    have hm1 : (1 : ℝ) ≤ c.modulus none := by exact_mod_cast c.modulus_pos none
    have hden : (c.length : ℝ) * ∏ j, ((s j).length : ℝ) ≤
        ((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hm1 hLc.le) hP.le
    have hscale' : (M : ℝ) /
        (((c.modulus none : ℝ) * c.length) * ∏ j, ((s j).length : ℝ)) ≤ V :=
      (div_le_div_of_nonneg_left (Nat.cast_nonneg M) (mul_pos hLc hP) hden).trans hscale
    have hq := (localizedMajorArcBudget_pos (n + 1) hU hζ).le
    have hd : (localizedMajorArcBudget (n + 1) U ζ *
        ((c.modulus none : ℝ) * U ^ (n + 1))) ^ J.card ≤
        (localizedMajorArcBudget (n + 1) U ζ * U ^ (n + 1 + 1)) ^ J.card := by
      apply pow_le_pow_left₀ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hq
      rw [pow_succ' U (n + 1)]
      exact mul_le_mul_of_nonneg_right hm (pow_nonneg hU0 _)
    apply weightedAffineModerateGridCoefficient_mem_major c s A hA hc h hζ hζ1
      ((localizedMajorArcLengthBudget_le_power (n + 1) hU hζ hζ1).trans hlong)
      (fun j => (localizedMajorArcLengthBudget_le_power (n + 1) hU hζ hζ1).trans
        (hlength.2.trans (hlen j))) u v hv hstride 0 hM J hJ
    · exact (hd.trans (majorArc_denominator_le_cover (n + 1) J.card hU hV hζ hζ1)).trans
        (hcover.2.1.trans (Nat.le_ceil _))
    · exact (majorArc_scaled_error_le_cover (n + 1) J.card hU hV hζ hζ1 hscale').trans
        (hcover.2.1.trans (Nat.le_ceil _))
    · exact hk
  · have hV4 : 0 ≤ 4 * V := by positivity
    have hbias : ζ ≤ ‖c.source.complexMean (fun z =>
        (FiniteProbabilityWeights.pi (fun j => (s j).source)).complexMean
          (fun x => CircleFourier.character (((z none : ℝ) *
            booleanBlockPhase (gridJetFrequency M J k) (fun j => affineCubeCoordinates (u j) (v j) (fun i => (x j i : ℝ))) : ℝ) :
              CircleFourier.Circle)))‖ := by
      simpa only [weightedAffineModerateGridCoefficient, zero_add] using hk
    obtain ⟨D, hD, hDb, a, ha⟩ := affine_weighted_positiveCoefficient_major_arc (T := (c.length : ℝ)) c.source
      (fun z => (z none : ℤ)) s A hA h hζ hζ1 (show 0 < (c.length : ℝ) / 4 by positivity)
      (fun z hz => ⟨hpositive z hz, by
        exact_mod_cast (Finset.mem_Ico.mp (z none).property).2.le⟩)
      (fun j => (localizedMajorArcLengthBudget_le_power n hU hζ hζ1).trans
        (hlength.1.trans (hlen j))) u v hv hstride (gridJetFrequency M J k) J hJ hbias
    have hraw : 0 ≤ (localizedMajorArcBudget n U ζ * U ^ (n + 1)) ^ J.card := by
      have := (localizedMajorArcBudget_pos n hU hζ).le
      positivity
    have hupper : 0 ≤ majorArcLengthConstant (n + 1) U /
        ζ ^ majorArcLengthExponent (n + 1) := by
      have := (majorArcLengthConstant_pos (n + 1) hU).le
      positivity
    have hDQ : (D : ℝ) ≤ positiveModerateCoverConstant n J.card U V /
        ζ ^ positiveModerateCoverExponent n J.card := hDb.trans
      ((mul_le_mul (lt_of_not_ge hlong).le
        (majorArc_denominator_le_cover n J.card hU hV4 hζ hζ1) hraw hupper).trans
          hcover.2.2)
    have hscale' : (M : ℝ) / (((c.length : ℝ) / 4) * ∏ j, ((s j).length : ℝ)) ≤
        4 * V := by
      calc
        _ = 4 * ((M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ))) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by norm_num)
    apply mem_rationalGridMajorBox hM k hD
      (by exact_mod_cast hDQ.trans (Nat.le_ceil _)) a
      (fun S => by simpa only [gridJetFrequency_apply] using ha S)
    exact (majorArc_scaled_error_le_cover n J.card hU hV4 hζ hζ1 hscale').trans
      (hcover.1.trans (Nat.le_ceil _))

theorem weightedPositiveAffineModerateGridCoefficient_minor_polynomial_s2_oai {n : ℕ} {I : Type*}
    [Fintype I] [DecidableEq I] (c : NormalizedScalarCubeSource Empty)
    (s : Fin (n + 1) → NormalizedScalarCubeSource I)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) {U V ζ : ℝ}
    (hc : ScalarCubePrimitiveBudget c A U) (h : ∀ j, ScalarCubePrimitiveBudget (s j) A U)
    (u : Fin (n + 1) → Option I → ℝ) (v : Fin (n + 1) → Option I → ℕ)
    (hv : ∀ j i, 0 < v j i) (hstride : ∀ j i, ((v j i * (s j).modulus i : ℕ) : ℝ) ≤ U)
    (hpositive : ∀ z, c.source.weight z ≠ 0 → (c.length : ℝ) / 4 ≤ (z none : ℝ))
    (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (hlen : ∀ j, positiveModerateLengthConstant n U / ζ ^ positiveModerateLengthExponent n ≤
      (s j).length)
    {M : ℕ} (hM : 0 < M)
    (hscale : (M : ℝ) / ((c.length : ℝ) * ∏ j, ((s j).length : ℝ)) ≤ V)
    (J : Finset (Finset I)) (hJ : ∀ S ∈ J, S.card ≤ n + 1)
    (k : J → Fin M) (hk : k ∉ polynomialGridCover J M (positiveModerateCoverConstant n J.card U V)
      (positiveModerateCoverExponent n J.card) ζ) :
    ‖weightedAffineModerateGridCoefficient c s u v 0 M J k‖ ≤ ζ := by
  exact le_of_lt (lt_of_not_ge (fun hh => hk
    (weightedPositiveAffineModerateGridCoefficient_mem_polynomial c s A hA hc h u v hv hstride hpositive
      hV hζ hζ1 hlen hM hscale J hJ k hh)))

end Erdos3

end

end OAI
end

theorem solution.{u_1} : type_of% @OAI.Erdos3.weightedPositiveAffineModerateGridCoefficient_minor_polynomial_s2_oai.{u_1} := @OAI.Erdos3.weightedPositiveAffineModerateGridCoefficient_minor_polynomial_s2_oai.{u_1}
