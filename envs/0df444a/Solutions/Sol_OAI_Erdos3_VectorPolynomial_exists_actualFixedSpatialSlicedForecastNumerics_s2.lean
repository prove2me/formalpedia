-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecastNumerics_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:35:20.438572+00:00
-- url     : https://prove2.me/submissions/dd2745b1-15b3-4600-88d3-f37aca9ca451

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B196
import Definitions.Def_OAIE3v2B301

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracy
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem uniformProductAccuracy_spec (N : ℕ) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 < δ) :
    0 < uniformProductAccuracy N C δ ∧ uniformProductAccuracy N C δ ≤ 1 ∧
      (N : ℝ) * uniformProductAccuracy N C δ * (C + 2) ^ N ≤ δ := by
  have hD : 0 < ((N : ℝ) + 1) * (C + 2) ^ N := by positivity
  have he : 0 < uniformProductAccuracy N C δ := lt_min zero_lt_one (div_pos hδ hD)
  refine ⟨he, min_le_left _ _, ?_⟩
  have hbound : uniformProductAccuracy N C δ * (((N : ℝ) + 1) * (C + 2) ^ N) ≤ δ :=
    (le_div_iff₀ hD).mp (min_le_right _ _)
  have hp : 0 ≤ uniformProductAccuracy N C δ * (C + 2) ^ N := by positivity
  nlinarith

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

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformScaledRetainedCharacters
namespace OAI

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

end Erdos3

end

section

namespace Erdos3

theorem uniformScaledRetainedFrequencyBound_nonneg (n d : ℕ) (U V ζ : ℝ) :
    0 ≤ uniformScaledRetainedFrequencyBound n d U V ζ := Nat.cast_nonneg _

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastModularCutoff
namespace OAI

section

namespace Erdos3

theorem exists_rationalForecast_order_cutoff {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    ∃ T : ℕ, 0 < T ∧ (T : ℝ) ≤ Real.exp (P + E + 2) ∧
      ∀ C : ℝ, C ≤ Real.exp P → C / T ≤ Real.exp (-E) := by
  let T := ⌈Real.exp (P + E)⌉₊
  have hlow : Real.exp (P + E) ≤ (T : ℝ) := Nat.le_ceil _
  have hT : 0 < T := by exact_mod_cast (Real.exp_pos (P + E)).trans_le hlow
  have hupp : (T : ℝ) ≤ Real.exp (P + E) + 1 := (Nat.ceil_lt_add_one
    (Real.exp_nonneg (P + E))).le
  have hbase : 1 ≤ Real.exp (P + E) := Real.one_le_exp (by linarith)
  have hexp2 : 2 ≤ Real.exp (2 : ℝ) := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  refine ⟨T, hT, ?_, ?_⟩
  · calc
      _ ≤ Real.exp (P + E) + 1 := hupp
      _ ≤ Real.exp (P + E) * Real.exp 2 := by nlinarith
      _ = _ := (Real.exp_add _ _).symm
  · intro C hC
    apply (div_le_iff₀ (by exact_mod_cast hT : (0 : ℝ) < T)).mpr
    calc
      _ ≤ Real.exp P := hC
      _ = Real.exp (-E) * Real.exp (P + E) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlow (Real.exp_nonneg _)

end Erdos3

end

section

namespace Erdos3

theorem exists_forecast_approximation_parameters (d : ℕ)
    {P E : ℝ} (hP : 0 ≤ P) (hE : 0 ≤ E) :
    ∃ (T : ℕ) (ε : ℝ),
      0 < T ∧ (T : ℝ) ≤ Real.exp (P + E + 3) ∧
      0 < ε ∧ ε ≤ 1 ∧
      ε⁻¹ ≤ Real.exp (E + 1 + d * (P + E + 3)) ∧
      ∀ C : ℝ, C ≤ Real.exp P →
        C / T + (T : ℝ) ^ d * ε ≤ Real.exp (-E) := by
  obtain ⟨T, hT, hTbound, htail⟩ := exists_rationalForecast_order_cutoff hP
    (show 0 ≤ E + 1 by linarith)
  have hTbound' : (T : ℝ) ≤ Real.exp (P + E + 3) := by
    convert hTbound using 1
    congr 1
    ring
  let Q := E + 1 + d * (P + E + 3)
  let ε := Real.exp (-Q)
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hε : 0 < ε := Real.exp_pos _
  have hε1 : ε ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hQ)
  have hεinv : ε⁻¹ ≤ Real.exp Q := by
    dsimp only [ε]
    rw [← Real.exp_neg, neg_neg]
  have hcount : (T : ℝ) ^ d * ε ≤ Real.exp (-(E + 1)) := by
    calc
      _ ≤ (Real.exp (P + E + 3)) ^ d * ε :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hTbound' d) hε.le
      _ = Real.exp (-(E + 1)) := by
        rw [← Real.exp_nat_mul]
        dsimp only [ε, Q]
        rw [← Real.exp_add]
        congr 1
        ring
  refine ⟨T, ε, hT, hTbound', hε, hε1, hεinv, ?_⟩
  intro C hC
  calc
    _ ≤ Real.exp (-(E + 1)) + Real.exp (-(E + 1)) := add_le_add (htail C hC) hcount
    _ = 2 * Real.exp (-(E + 1)) := (two_mul _).symm
    _ ≤ Real.exp 1 * Real.exp (-(E + 1)) :=
      mul_le_mul_of_nonneg_right (by linarith [Real.add_one_le_exp (1 : ℝ)])
        (Real.exp_nonneg _)
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

theorem exists_forecast_weighted_approximation_parameters (d : ℕ)
    {Psm Pin Pdec E : ℝ} (hPsm : 0 ≤ Psm) (hPin : 0 ≤ Pin)
    (hPdec : 0 ≤ Pdec) (hE : 0 ≤ E) :
    ∃ (T : ℕ) (ε : ℝ),
      0 < T ∧ (T : ℝ) ≤ Real.exp (Pin + Pdec + (E + Psm) + 3) ∧
      0 < ε ∧ ε ≤ 1 ∧
      ε⁻¹ ≤ Real.exp (E + Psm + 1 + d * (Pin + Pdec + (E + Psm) + 3)) ∧
      ∀ H I C : ℝ, 0 ≤ H → 0 ≤ C → H ≤ Real.exp Psm → I ≤ Real.exp Pin →
        C ≤ Real.exp Pdec →
        H * (I * (C / T) + (T : ℝ) ^ d * ε) ≤ Real.exp (-E) := by
  obtain ⟨T, ε, hT, hTbound, hε, hε1, hεinv, herr⟩ :=
    exists_forecast_approximation_parameters d (add_nonneg hPin hPdec) (add_nonneg hE hPsm)
  refine ⟨T, ε, hT, hTbound, hε, hε1, hεinv, ?_⟩
  intro H I C hH hC hHcap hIcap hCcap
  have hIC : I * C ≤ Real.exp (Pin + Pdec) := by
    rw [Real.exp_add]
    exact mul_le_mul hIcap hCcap hC (Real.exp_nonneg _)
  have herror := herr (I * C) hIC
  rw [mul_div_assoc] at herror
  calc
    _ ≤ H * Real.exp (-(E + Psm)) := mul_le_mul_of_nonneg_left herror hH
    _ ≤ Real.exp Psm * Real.exp (-(E + Psm)) :=
      mul_le_mul_of_nonneg_right hHcap (Real.exp_nonneg _)
    _ = Real.exp (-E) := by rw [← Real.exp_add]; congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem modularForecastRankConstant_decay (s D : ℕ) :
    modularRankDecayExponent s (modularForecastRankConstant s D : ℝ) = (D + 2 : ℕ) := by
  unfold modularRankDecayExponent modularForecastRankConstant
  push_cast
  have htwo : (2 : ℝ) ^ s ≠ 0 := by positivity
  have hfac : (s.factorial : ℝ) ≠ 0 := by positivity
  field_simp

end Erdos3

end

section

namespace Erdos3

theorem forecastModularCharge_exp_bound (m D Rbad Qpres : ℕ)
    {Pbad Ppres : ℝ} (hR : (Rbad : ℝ) ≤ Real.exp Pbad)
    (hQ : (Qpres : ℝ) ≤ Real.exp Ppres) :
    ((Rbad * Qpres : ℕ) : ℝ) ^
      (modularRankDecayExponent m (modularForecastRankConstant m D : ℝ) *
        modularRankChargeFactor m) ≤
      Real.exp ((Pbad + Ppres) * ((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) := by
  rw [modularForecastRankConstant_decay]
  have hbase : ((Rbad * Qpres : ℕ) : ℝ) ≤ Real.exp (Pbad + Ppres) := by
    rw [Nat.cast_mul, Real.exp_add]
    exact mul_le_mul hR hQ (Nat.cast_nonneg _) (Real.exp_nonneg _)
  calc
    _ ≤ (Real.exp (Pbad + Ppres)) ^
        (((D + 2 : ℕ) : ℝ) * modularRankChargeFactor m) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) hbase (by positivity)
    _ = _ := by rw [← Real.exp_mul, mul_assoc]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.IntegerSupportTorus
namespace OAI

section

namespace Erdos3

theorem integerSupportTorusFactor_upper {H : ℝ} (hH : 0 ≤ H) :
    (integerSupportTorusFactor H : ℝ) ≤ 2 * H + 3 := by
  have h := Nat.ceil_lt_add_one hH
  simp only [integerSupportTorusFactor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.WeightedBlockTorus
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem blockTorusFactor_upper (q h b : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    (blockTorusFactor q h b A : ℝ) ≤ 2 * blockJetScaleBound q h b A + 3 :=
  integerSupportTorusFactor_upper (blockJetScaleBound_nonneg q h b hA)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ShortIntegerCubeBudget
namespace OAI

section

namespace Erdos3

theorem inactiveDenominator_le_exp {γ p : ℝ} (hγ : 0 < γ) (hp : 0 ≤ p)
    (hγp : γ⁻¹ ≤ Real.exp p) :
    (inactiveDenominator γ : ℝ) ≤ Real.exp (p+1) := by
  simp only [inactiveDenominator, Nat.cast_max, Nat.cast_one]
  exact max_le (Real.one_le_exp_iff.mpr (by linarith))
    (natCeil_le_exp_succ (by positivity) hp hγp)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.FixedPrincipalCoefficientSpectrum
namespace OAI

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

end Erdos3

end

section

namespace Erdos3

theorem positiveRetainedFrequencyBound_nonneg (n d : ℕ) (U V ζ : ℝ) :
    0 ≤ positiveRetainedFrequencyBound n d U V ζ := Nat.cast_nonneg _

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedInactiveSupportBudget
namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem two_mul_add_three_exp_bound {x P : ℝ} (hP : 0 ≤ P) (hx : x ≤ Real.exp P) :
    2 * x + 3 ≤ Real.exp (P + 4) := by
  have h1 := Real.one_le_exp_iff.mpr hP
  have h5 : (5 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  calc
    _ ≤ 5 * Real.exp P := by linarith
    _ ≤ Real.exp 4 * Real.exp P := mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add, add_comm]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSlicedGridGeometryBudget
namespace OAI

section

namespace Erdos3

theorem principalProfileSize_exp_bounds (b : ℕ) {R D v : ℝ}
    (hR : 0 < R) (hb : (b : ℝ) ≤ D) (hRv : R ≤ Real.exp v) (hRi : R⁻¹ ≤ Real.exp v) :
    principalProfileSize R b ≤ Real.exp v ∧
      (principalProfileSize R b)⁻¹ ≤ Real.exp (D + v + 8) := by
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hden : (1 : ℝ) ≤ 8 * ((b : ℝ) + 1) := by linarith
  have hfirst : principalProfileSize R b ≤ R := div_le_self hR.le hden
  have hbexp : (b : ℝ) + 1 ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  refine ⟨hfirst.trans hRv, ?_⟩
  rw [principalProfileSize, inv_div, div_eq_mul_inv]
  have he := mul_le_mul (mul_le_mul h8 hbexp (by positivity) (Real.exp_nonneg _)) hRi
    (inv_nonneg.mpr hR.le) (by positivity)
  exact he.trans_eq (by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring)

namespace VectorPolynomial
variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "denom" => inactiveDenominator gamma

omit [Fintype G] [∀ j, Fintype (I j)] in
theorem allocatedSlicedGridHeightCutoff_exp_bound [Fintype G] [∀ j, Fintype (I j)]
    (hR : 0 < R j) (T : ℕ) {v t : ℝ}
    (hv : 0 ≤ v) (ht : 0 ≤ t) (hγv : gamma⁻¹ ≤ Real.exp v) (hT : (T : ℝ) ≤ Real.exp t) :
    (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T : ℝ) ≤
      Real.exp ((layerTailDegree m + 1 : ℕ) * t + (j.val + 1 : ℕ) * (t + 1) + 2 * v + 5) := by
  have hden := inactiveDenominator_le_exp (principalProfileSize_pos hR _) hv hγv
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hTa := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg T) hT ht (layerTailDegree m + 1) le_rfl
  have hTi := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg T) hT ht (j.val + 1) le_rfl
  have hpow2 : (2 : ℝ) ^ (j.val + 1) ≤ Real.exp (j.val + 1 : ℕ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) (j.val + 1) le_rfl
  have hmid : (denom : ℝ) * 2 ^ (j.val + 1) * (T : ℝ) ^ (j.val + 1) ≤
      Real.exp (v + 1 + (j.val + 1 : ℕ) * (t + 1)) := by
    have hb := mul_le_mul (mul_le_mul hden hpow2 (by positivity) (Real.exp_nonneg _))
      hTi (by positivity) (by positivity)
    simp only [← Real.exp_add] at hb
    exact hb.trans_eq (by congr 1; ring)
  have hlast : (2 : ℝ) * denom ≤ Real.exp (v + 2) := by
    have hb := mul_le_mul htwo hden (Nat.cast_nonneg _) (Real.exp_nonneg _)
    exact hb.trans_eq (by rw [← Real.exp_add]; congr 1; ring)
  have hsum := add_le_exp_add_one (by positivity) (by positivity) hTa hmid
  have hsum' := add_le_exp_add_one (by positivity) (by positivity) hsum hlast
  simp only [allocatedSlicedGridHeightCutoff, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  exact hsum'.trans_eq (by congr 1; push_cast; ring)

end VectorPolynomial
end Erdos3

end

section

namespace Erdos3

theorem blockTorusFactor_exp_bound (q h b : ℕ) {A D v : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hA : 0 ≤ A)
    (hq : (q : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) (hb : (b : ℝ) ≤ D)
    (hAv : A ≤ Real.exp v) :
    (blockTorusFactor q h b A : ℝ) ≤ Real.exp (D ^ 2 + 2 * D + v + 4) := by
  have hbexp : (b : ℝ) ≤ Real.exp D := hb.trans (by linarith [Real.add_one_le_exp D])
  have hqexp : ((q + 1 : ℕ) : ℝ) ≤ Real.exp D := by
    push_cast
    linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowtwo : (2 : ℝ) ^ h ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) h hh
  have hpowq := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg (q + 1)) hqexp hD h hh
  have hblock : blockJetScaleBound q h b A ≤ Real.exp (D ^ 2 + 2 * D + v) := by
    unfold blockJetScaleBound
    calc
      _ ≤ Real.exp D * Real.exp D * Real.exp (D * D) * Real.exp v := by gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  exact (blockTorusFactor_upper q h b hA).trans
    (two_mul_add_three_exp_bound (by positivity) hblock)

theorem div_density_pow_exp_bound {X δ t w : ℝ} (n : ℕ)
    (_hX : 0 ≤ X) (hδ : 0 < δ) (hXt : X ≤ Real.exp t) (hδw : δ⁻¹ ≤ Real.exp w) :
    X / δ ^ n ≤ Real.exp (t + n * w) := by
  rw [div_eq_mul_inv, ← inv_pow]
  have hp : (δ⁻¹) ^ n ≤ Real.exp (n * w) := by
    calc
      _ ≤ (Real.exp w) ^ n := pow_le_pow_left₀ (inv_nonneg.mpr hδ.le) hδw n
      _ = _ := by rw [← Real.exp_nat_mul]
  exact (mul_le_mul hXt hp (by positivity) (Real.exp_nonneg _)).trans_eq (Real.exp_add _ _).symm

theorem slicedGrid_fourier_geometry_exp_bounds {Ta Ti γ C δ t v c w : ℝ}
    (hTa : 0 ≤ Ta) (hTi : 0 ≤ Ti) (hγ : 0 < γ) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hTat : Ta ≤ Real.exp t) (hTit : Ti ≤ Real.exp t)
    (hγv : γ⁻¹ ≤ Real.exp v) (hCc : C ≤ Real.exp c) (hδw : δ⁻¹ ≤ Real.exp w)
    (degree d ta ti : ℕ) :
    (Ta / (2 * γ)) / δ ^ degree ≤ Real.exp (t + v + degree * w) ∧
    (Ti * C) / δ ^ degree ≤ Real.exp (t + c + degree * w) ∧
    Ta ^ d / δ ^ ta ≤ Real.exp (d * t + ta * w) ∧
    (Ti * C) ^ d / δ ^ ti ≤ Real.exp (d * (t + c) + ti * w) := by
  have hactive : Ta / (2 * γ) ≤ Real.exp (t + v) := by
    calc
      _ ≤ Ta / γ := div_le_div_of_nonneg_left hTa hγ (by linarith)
      _ = Ta * γ⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp t * Real.exp v := mul_le_mul hTat hγv (inv_nonneg.mpr hγ.le) (Real.exp_nonneg _)
      _ = _ := (Real.exp_add _ _).symm
  have hinactive : Ti * C ≤ Real.exp (t + c) :=
    (mul_le_mul hTit hCc hC (Real.exp_nonneg _)).trans_eq (Real.exp_add _ _).symm
  refine ⟨div_density_pow_exp_bound degree (by positivity) hδ hactive hδw,
    div_density_pow_exp_bound degree (by positivity) hδ hinactive hδw, ?_, ?_⟩
  · apply div_density_pow_exp_bound ta (by positivity) hδ _ hδw
    calc
      _ ≤ (Real.exp t) ^ d := pow_le_pow_left₀ hTa hTat d
      _ = _ := by rw [← Real.exp_nat_mul]
  · apply div_density_pow_exp_bound ti (by positivity) hδ _ hδw
    calc
      _ ≤ (Real.exp (t + c)) ^ d := pow_le_pow_left₀ (mul_nonneg hTi hC) hinactive d
      _ = _ := by rw [← Real.exp_nat_mul]

theorem slicedGrid_support_exp_bound (q h d : ℕ) {C R D v : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hq : (q : ℝ) ≤ D) (hh : (h : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (hCv : C ≤ Real.exp v) (hRv : R ≤ Real.exp v) :
    (d : ℝ) * (C * (2 ^ q * ((q : ℝ) + 1) ^ h) * R) + 1 / 4 ≤
      Real.exp (D ^ 2 + 2 * D + 2 * v + 1) := by
  have hdexp : (d : ℝ) ≤ Real.exp D := hd.trans (by linarith [Real.add_one_le_exp D])
  have hqexp : (q : ℝ) + 1 ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp2 : (2 : ℝ) ^ q ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) q hq
  have hpq := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ (q : ℝ) + 1) hqexp hD h hh
  have hbound : (d : ℝ) * (C * (2 ^ q * ((q : ℝ) + 1) ^ h) * R) ≤
      Real.exp (D ^ 2 + 2 * D + 2 * v) := by
    calc
      _ ≤ Real.exp D * (Real.exp v * (Real.exp D * Real.exp (D * D)) * Real.exp v) := by gcongr
      _ = _ := by simp only [← Real.exp_add]; congr 1; ring
  have hsum := add_le_exp_add_one (by positivity : 0 ≤ D ^ 2 + 2 * D + 2 * v)
    (by norm_num : (0 : ℝ) ≤ 0) hbound (by norm_num : (1 / 4 : ℝ) ≤ Real.exp 0)
  simpa only [add_zero] using hsum

end Erdos3

end

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j)) (q d T : ℕ)
local notation "degree" => j.val + 1
local notation "b" => Fintype.card (B (Sigma.mk j (Sum.inr i)))
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
local notation "cost" => (inactiveDenominator gamma : ℝ) * 2 ^ degree
local notation "torusA" => blockTorusFactor q degree b (4 * gamma)
local notation "torusI" => blockTorusFactor q degree b 1

theorem allocatedSlicedGrid_geometry_bounds {δ D v w t : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t)
    (hδ : 0 < δ) (hR : 0 < R j)
    (hq : (q : ℝ) ≤ D) (hdegree : ((degree : ℕ) : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D) (hb : (b : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v) :
    let p := slicedGridGeometryLog D v w t
    ((torusA : ℝ) / (2 * gamma)) / δ ^ degree ≤ Real.exp p ∧
    (torusI : ℝ) * cost / δ ^ degree ≤ Real.exp p ∧
    (torusA : ℝ) ^ d / δ ^ ((layerTailDegree m + 1) * d) ≤ Real.exp p ∧
    ((torusI : ℝ) * cost) ^ d / δ ^ (degree * d) ≤ Real.exp p ∧
    (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T : ℝ) ≤ Real.exp p ∧
    (d : ℝ) * ((Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
      ((2 : ℝ) ^ q * ((q : ℝ) + 1) ^ degree) * R j) + 1 / 4 ≤ Real.exp p := by
  intro p
  let g := D + v + 8
  let tau := D ^ 2 + 2 * D + v + 8
  let c := g + D + 1
  let Z := tau + c + D * w
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have htau : 0 ≤ tau := by dsimp [tau]; positivity
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hZ : 0 ≤ Z := by dsimp [Z]; positivity
  have hγ : 0 < gamma := principalProfileSize_pos hR _
  have hslots : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hb
  obtain ⟨hγupper, hγinv⟩ := principalProfileSize_exp_bounds _ hR hslots hRv hRi
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hA : 4 * gamma ≤ Real.exp (v + 4) := by
    exact (mul_le_mul h4 hγupper hγ.le (Real.exp_nonneg _)).trans_eq (by rw [← Real.exp_add, add_comm])
  have hTa : (torusA : ℝ) ≤ Real.exp tau := by
    have h := blockTorusFactor_exp_bound q degree b hD (by positivity) (by positivity) hq hdegree hb hA
    convert h using 1
    dsimp [tau]
    ring_nf
  have hTi : (torusI : ℝ) ≤ Real.exp tau := by
    have h := blockTorusFactor_exp_bound q degree b hD (by positivity : 0 ≤ v + 4)
      (by norm_num : (0 : ℝ) ≤ 1) hq hdegree hb (Real.one_le_exp_iff.mpr (by positivity))
    convert h using 1
    dsimp [tau]
    ring_nf
  have hden := inactiveDenominator_le_exp hγ hg hγinv
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp2 : (2 : ℝ) ^ degree ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) degree hdegree
  have hcost : cost ≤ Real.exp c := by
    exact (mul_le_mul hden hp2 (by positivity) (Real.exp_nonneg _)).trans_eq (by
      rw [← Real.exp_add]; dsimp [c]; congr 1; ring)
  obtain ⟨hVa, hVi, hWa, hWi⟩ := slicedGrid_fourier_geometry_exp_bounds
    (Nat.cast_nonneg torusA) (Nat.cast_nonneg torusI) hγ (by positivity) hδ hTa hTi hγinv hcost hδw
    degree d ((layerTailDegree m + 1) * d) (degree * d)
  have hbase0 : 0 ≤ (D + 1) * Z := by positivity
  have hcut0 : 0 ≤ 2 * D * t + D + 2 * g + 5 := by positivity
  have hsup0 : 0 ≤ D ^ 2 + 2 * D + 2 * v + 1 := by positivity
  have hbase : (D + 1) * Z ≤ p := by
    change (D + 1) * Z ≤ (D + 1) * Z + (2 * D * t + D + 2 * g + 5) + (D ^ 2 + 2 * D + 2 * v + 1)
    linarith only [hcut0, hsup0]
  have hsingle : Z ≤ p := (by nlinarith only [mul_nonneg hD hZ] : Z ≤ (D + 1) * Z).trans hbase
  have hprod : D * Z ≤ p := (by nlinarith only [hZ] : D * Z ≤ (D + 1) * Z).trans hbase
  have hcut : 2 * D * t + D + 2 * g + 5 ≤ p := by
    change _ ≤ (D + 1) * Z + (2 * D * t + D + 2 * g + 5) + (D ^ 2 + 2 * D + 2 * v + 1)
    linarith only [hbase0, hsup0]
  have hsup : D ^ 2 + 2 * D + 2 * v + 1 ≤ p := by
    change _ ≤ (D + 1) * Z + (2 * D * t + D + 2 * g + 5) + (D ^ 2 + 2 * D + 2 * v + 1)
    linarith only [hbase0, hcut0]
  refine ⟨hVa.trans (Real.exp_le_exp.mpr ?_), hVi.trans (Real.exp_le_exp.mpr ?_),
    hWa.trans (Real.exp_le_exp.mpr ?_), hWi.trans (Real.exp_le_exp.mpr ?_), ?_, ?_⟩
  · apply le_trans _ hsingle
    change tau + g + _ ≤ tau + (g + D + 1) + D * w
    linarith only [hD, mul_le_mul_of_nonneg_right hdegree hw]
  · apply le_trans _ hsingle
    dsimp [Z]
    linarith only [mul_le_mul_of_nonneg_right hdegree hw]
  · apply le_trans _ hprod
    simp only [Nat.cast_mul]
    calc
      _ ≤ D * tau + (D * D) * w := by gcongr
      _ ≤ D * Z := by dsimp [Z]; nlinarith only [mul_nonneg hD hc]
  · apply le_trans _ hprod
    simp only [Nat.cast_mul]
    calc
      _ ≤ D * (tau + c) + (D * D) * w := by gcongr
      _ = D * Z := by dsimp [Z]; ring
  · apply (allocatedSlicedGridHeightCutoff_exp_bound B R j i hR T hg ht hγinv hT).trans
    apply Real.exp_le_exp.mpr
    apply le_trans _ hcut
    calc
      _ ≤ D * t + D * (t + 1) + 2 * g + 5 := by gcongr
      _ = _ := by ring
  · exact (slicedGrid_support_exp_bound q degree d hD hv (by positivity) hR.le hq hdegree hd hcoeff hRv).trans
      (Real.exp_le_exp.mpr hsup)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformProductAccuracyLogBounds
namespace OAI

section

namespace Erdos3

theorem uniformProductAccuracy_inverse_exp_bound (N : ℕ) {C δ D T E : ℝ}
    (hC : 0 ≤ C) (hδ : 0 < δ) (hD : 0 ≤ D) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hN : (N : ℝ) ≤ D) (hCT : C ≤ Real.exp T) (hδE : δ⁻¹ ≤ Real.exp E) :
    (uniformProductAccuracy N C δ)⁻¹ ≤ Real.exp (uniformProductAccuracyLog D T E) := by
  have hNexp : (N : ℝ) + 1 ≤ Real.exp D := by linarith [Real.add_one_le_exp D]
  have hCexp : C + 2 ≤ Real.exp (T + 4) :=
    (by linarith : C + 2 ≤ 2 * C + 3).trans (two_mul_add_three_exp_bound hT hCT)
  have hpow := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ C + 2)
    hCexp (by positivity) N hN
  have hden : ((N : ℝ) + 1) * (C + 2) ^ N ≤ Real.exp (D + D * (T + 4)) :=
    (mul_le_mul hNexp hpow (by positivity) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  unfold uniformProductAccuracy
  apply inv_min_le_of_inv_le
  · rw [inv_one]
    exact Real.one_le_exp_iff.mpr (uniformProductAccuracyLog_nonneg hD hT hE)
  · rw [inv_div, div_eq_mul_inv]
    exact (mul_le_mul hden hδE (inv_nonneg.mpr hδ.le) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Fourier.UniformSpectrumLogBounds
namespace OAI

section

namespace Erdos3

theorem majorArcConstants_exp_bounds (n : ℕ) {U p : ℝ}
    (hU : 0 ≤ U) (hp : 0 ≤ p) (hUp : U ≤ Real.exp p) :
    majorArcBiasConstant n U ≤ Real.exp (majorArcBiasLog n p) ∧
      majorArcLocalizationConstant n U ≤ Real.exp (majorArcLocalizationLog n p) ∧
      majorArcLengthConstant n U ≤ Real.exp (majorArcLengthLog n p) ∧
      majorArcErrorConstant n U ≤ Real.exp (majorArcErrorLog n p) := by
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hU2 : U ^ 2 ≤ Real.exp (2 * p) :=
    pow_le_exp_mul_of_le_exp hU hUp hp 2 le_rfl
  have hbase : 2 * U ^ 2 ≤ Real.exp (1 + 2 * p) :=
    (mul_le_mul htwo hU2 (sq_nonneg U) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hbpow := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * U ^ 2)
    hbase (by positivity) ((n + 1) * majorArcBiasExponent n) le_rfl
  let c : ℕ := denseProductDensityConstant n * (2 * 3 ^ n) ^ denseProductExponent n
  have hc : (c : ℝ) ≤ Real.exp (c : ℝ) := by linarith [Real.add_one_le_exp (c : ℝ)]
  have hb : majorArcBiasConstant n U ≤ Real.exp (majorArcBiasLog n p) := by
    calc
      _ = (c : ℝ) * (2 * U ^ 2) ^ ((n + 1) * majorArcBiasExponent n) := by
        simp only [majorArcBiasConstant, c, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
      _ ≤ Real.exp (c : ℝ) * Real.exp (((n + 1) * majorArcBiasExponent n : ℕ) * (1 + 2 * p)) :=
        mul_le_mul hc hbpow (by positivity) (Real.exp_pos _).le
      _ = _ := (Real.exp_add _ _).symm
  have hU6 : U ^ 6 ≤ Real.exp (6 * p) :=
    pow_le_exp_mul_of_le_exp hU hUp hp 6 le_rfl
  have hlpow := pow_le_exp_mul_of_le_exp (by positivity : 0 ≤ 2 * U ^ 2)
    hbase (by positivity) ((n + 1) * 2) le_rfl
  have h256 : (256 : ℝ) ≤ Real.exp 256 := by linarith [Real.add_one_le_exp (256 : ℝ)]
  have hl : majorArcLocalizationConstant n U ≤ Real.exp (majorArcLocalizationLog n p) := by
    unfold majorArcLocalizationConstant majorArcLocalizationLog
    calc
      _ ≤ Real.exp 256 * Real.exp (6 * p) * Real.exp (((n + 1) * 2 : ℕ) * (1 + 2 * p)) := by
        gcongr
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  obtain ⟨hb0, hl0, _, _⟩ := majorArcBaseLogs_nonneg n hp
  have hbc : 0 ≤ majorArcBiasConstant n U := by unfold majorArcBiasConstant; positivity
  have hlc : 0 ≤ majorArcLocalizationConstant n U := by unfold majorArcLocalizationConstant; positivity
  have hplus : majorArcBiasConstant n U + 1 ≤ Real.exp (majorArcBiasLog n p + 1) := by
    rw [add_comm]
    exact one_add_le_exp_succ hb0 hb
  have hlength : majorArcLengthConstant n U ≤ Real.exp (majorArcLengthLog n p) := by
    have hmul := (mul_le_mul hl hplus (by positivity) (Real.exp_pos _).le).trans_eq
      (Real.exp_add _ _).symm
    exact hmul.trans_eq (by unfold majorArcLengthLog; congr 1; ring)
  have hlpow' := pow_le_exp_mul_of_le_exp hlc hl hl0 (n + 1) le_rfl
  have herror : majorArcErrorConstant n U ≤ Real.exp (majorArcErrorLog n p) :=
    (mul_le_mul hb hlpow' (pow_nonneg hlc _) (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  exact ⟨hb, hl, hlength, herror⟩

theorem majorArcCoverConstant_exp_bound (n j : ℕ) {U V p v : ℝ}
    (hU : 0 ≤ U) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) :
    majorArcCoverConstant n j U V ≤ Real.exp (majorArcCoverLog n j p v) := by
  obtain ⟨hb, _, _, he⟩ := majorArcConstants_exp_bounds n hU hp hUp
  obtain ⟨hb0, _, _, he0⟩ := majorArcBaseLogs_nonneg n hp
  have hbc : 0 ≤ majorArcBiasConstant n U := by unfold majorArcBiasConstant; positivity
  have hec : 0 ≤ majorArcErrorConstant n U := by
    unfold majorArcErrorConstant majorArcBiasConstant majorArcLocalizationConstant
    positivity
  have hUpow := pow_le_exp_mul_of_le_exp hU hUp hp (n + 1) le_rfl
  have hmul := (mul_le_mul hb hUpow (pow_nonneg hU _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hpow := pow_le_exp_mul_of_le_exp (mul_nonneg hbc (pow_nonneg hU _)) hmul
    (by positivity) j le_rfl
  have hfirst := one_add_le_exp_succ
    (by positivity : 0 ≤ (j : ℝ) * (majorArcBiasLog n p + (n + 1 : ℕ) * p)) hpow
  have hsecond := (mul_le_mul hVv he hec (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ (j : ℝ) * (majorArcBiasLog n p + (n + 1 : ℕ) * p) + 1)
    (add_nonneg hv he0) hfirst hsecond
  exact hsum.trans_eq (by unfold majorArcCoverLog; congr 1; ring)

end Erdos3

end

section

namespace Erdos3

theorem majorArcSpectrumConstant_exp_bound (n j : ℕ) {U V p v : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) :
    majorArcSpectrumConstant n j U V ≤ Real.exp (majorArcSpectrumLog n j p v) := by
  have hc := majorArcCoverConstant_exp_bound n j (zero_le_one.trans hU) hp hv hUp hVv
  have hc0 := zero_le_one.trans (majorArcCoverConstant_one_le n j hU hV)
  have hlog := majorArcCoverLog_nonneg n j hp hv
  have hp4 := pow_le_exp_mul_of_le_exp hc0 hc hlog 4 le_rfl
  have h195 : (195 : ℝ) ≤ Real.exp 195 := by linarith [Real.add_one_le_exp (195 : ℝ)]
  have hbase := (mul_le_mul h195 hp4 (pow_nonneg hc0 _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  exact pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) j le_rfl

theorem uniformBlockSpectrumAccuracy_exp_bound (n j t : ℕ) {U V W p v w : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w) :
    uniformBlockSpectrumAccuracyConstant n j t U V W + 1 ≤
      Real.exp (uniformBlockAccuracyLog n j t p v w) := by
  have hlen := (majorArcConstants_exp_bounds n (zero_le_one.trans hU) hp hUp).2.2.1
  have hspec := majorArcSpectrumConstant_exp_bound n j hU hV hp hv hUp hVv
  have hL := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hS := (uniformSpectrumLogs_nonneg n j t hp hv hw).1
  have hlen0 := (majorArcLengthConstant_pos n hU).le
  have hspec0 := majorArcSpectrumConstant_nonneg n j U V
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowS : (2 : ℝ) ^ majorArcSpectrumExponent n j ≤
      Real.exp (majorArcSpectrumExponent n j : ℝ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (majorArcSpectrumExponent n j) le_rfl
  have hpowL : (2 : ℝ) ^ majorArcLengthExponent n ≤ Real.exp (majorArcLengthExponent n : ℝ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (majorArcLengthExponent n) le_rfl
  have hfirst : 2 * majorArcSpectrumConstant n j U V * 2 ^ majorArcSpectrumExponent n j ≤
      Real.exp (1 + majorArcSpectrumLog n j p v + (majorArcSpectrumExponent n j : ℝ)) := by
    have hh := mul_le_mul (mul_le_mul htwo hspec hspec0 (Real.exp_pos _).le) hpowS
      (by positivity) (by positivity)
    simpa only [← Real.exp_add] using hh
  have hbase := (mul_le_mul hpowL hlen hlen0 (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hbasepow := pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) t le_rfl
  have hsecond := (mul_le_mul hWw hbasepow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ 1 + majorArcSpectrumLog n j p v + (majorArcSpectrumExponent n j : ℝ))
    (by positivity : 0 ≤ w + (t : ℝ) * ((majorArcLengthExponent n : ℝ) + majorArcLengthLog n p))
    hfirst hsecond
  have hplus := one_add_le_exp_succ (by positivity) hsum
  calc
    _ = 1 + (2 * majorArcSpectrumConstant n j U V * 2 ^ majorArcSpectrumExponent n j +
        W * (2 ^ majorArcLengthExponent n * majorArcLengthConstant n U) ^ t) := by
      unfold uniformBlockSpectrumAccuracyConstant
      ring
    _ ≤ _ := hplus
    _ = _ := by unfold uniformBlockAccuracyLog; congr 1; ring

theorem uniformSpectrumSizeConstant_exp_bound (n j t : ℕ) {U V W p v w : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w) :
    uniformSpectrumSizeConstant n j t U V W ≤ Real.exp (uniformSpectrumSizeLog n j t p v w) := by
  have hS := majorArcSpectrumConstant_exp_bound n j hU hV hp hv hUp hVv
  have hL := (majorArcConstants_exp_bounds n (zero_le_one.trans hU) hp hUp).2.2.1
  have hA := uniformBlockSpectrumAccuracy_exp_bound n j t hU hV hp hv hw hUp hVv hWw
  have hL0 := (majorArcBaseLogs_nonneg n hp).2.2.1
  obtain ⟨hS0, hA0, _⟩ := uniformSpectrumLogs_nonneg n j t hp hv hw
  have hlen0 := (majorArcLengthConstant_pos n hU).le
  have hspec0 := majorArcSpectrumConstant_nonneg n j U V
  have hLt := pow_le_exp_mul_of_le_exp hlen0 hL hL0 t le_rfl
  have hsecond := (mul_le_mul hWw hLt (pow_nonneg hlen0 _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hsum := add_le_exp_add_one hS0 (by positivity) hS hsecond
  have haccuracy0 : 0 ≤ uniformBlockSpectrumAccuracyConstant n j t U V W + 1 := by
    unfold uniformBlockSpectrumAccuracyConstant
    positivity
  have hpow := pow_le_exp_mul_of_le_exp haccuracy0 hA hA0
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t)) le_rfl
  exact (mul_le_mul hsum hpow (pow_nonneg haccuracy0 _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm

theorem uniformSpectrumAbsoluteCap_exp_bound (n j t : ℕ) {U V W p v w : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w) :
    uniformSpectrumAbsoluteCap n j t U V W ≤ Real.exp (uniformSpectrumSizeLog n j t p v w + 1) := by
  have hbound := uniformSpectrumSizeConstant_exp_bound n j t hU hV hW hp hv hw hUp hVv hWw
  have hplus := one_add_le_exp_succ (uniformSpectrumLogs_nonneg n j t hp hv hw).2.2 hbound
  simpa only [uniformSpectrumAbsoluteCap, add_comm] using hplus

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformScaledRetainedLogBounds
namespace OAI

section

namespace Erdos3

theorem uniformBlockRetainedBias_inverse_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    (uniformBlockRetainedBias n j t U V W ε)⁻¹ ≤
      Real.exp (uniformRetainedBiasLog n j t p v w E) := by
  have hA := uniformBlockSpectrumAccuracy_exp_bound n j t hU hV hp hv hw hUp hVv hWw
  rw [uniformBlockRetainedBias_eq n j t hU hW hε1, inv_div, div_eq_mul_inv]
  exact (mul_le_mul hA hεE (inv_nonneg.mpr hε.le) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm

theorem uniformSpectrumCardBound_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    uniformSpectrumSizeConstant n j t U V W /
        ε ^ max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t) ≤
      Real.exp (uniformSpectrumCardLog n j t p v w E) := by
  have hS := uniformSpectrumSizeConstant_exp_bound n j t hU hV hW hp hv hw hUp hVv hWw
  have hpow := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hε.le) hεE hE
    (max (majorArcSpectrumExponent n j) (majorArcLengthExponent n * t)) le_rfl
  have hbound := (mul_le_mul hS hpow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  simpa only [uniformSpectrumCardLog, div_eq_mul_inv, inv_pow] using hbound

theorem uniformRetainedFrequency_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    2 * majorArcCoverConstant n j U V /
        (uniformBlockRetainedBias n j t U V W ε) ^ majorArcCoverExponent n j ≤
      Real.exp (uniformRetainedFrequencyLog n j t p v w E) := by
  have hζ : 0 ≤ uniformBlockRetainedBias n j t U V W ε :=
    (uniformBlockRetainedBias_spec n j t hU hW hε).1.le
  have hB := uniformBlockRetainedBias_inverse_exp_bound n j t hU hV hW hε hε1 hp hv hw
    hUp hVv hWw hεE
  have hB0 := (uniformRetainedLogs_nonneg n j t hp hv hw hE).1
  have hC := majorArcCoverConstant_exp_bound n j (zero_le_one.trans hU) hp hv hUp hVv
  have hC0 := zero_le_one.trans (majorArcCoverConstant_one_le n j hU hV)
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hbase := (mul_le_mul htwo hC hC0 (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hpow := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (majorArcCoverExponent n j) le_rfl
  have hbound := (mul_le_mul hbase hpow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  simpa only [uniformRetainedFrequencyLog, div_eq_mul_inv, inv_pow] using hbound

theorem uniformCharacterDenominatorBound_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    uniformCharacterDenominatorBound n j t U V W (uniformBlockRetainedBias n j t U V W ε) ≤
      Real.exp (uniformRetainedDenominatorLog n j t p v w E) := by
  let ζ := uniformBlockRetainedBias n j t U V W ε
  have hζ : 0 ≤ ζ := (uniformBlockRetainedBias_spec n j t hU hW hε).1.le
  have hB := uniformBlockRetainedBias_inverse_exp_bound n j t hU hV hW hε hε1 hp hv hw
    hUp hVv hWw hεE
  have hB0 := (uniformRetainedLogs_nonneg n j t hp hv hw hE).1
  have hC := majorArcCoverConstant_exp_bound n j (zero_le_one.trans hU) hp hv hUp hVv
  have hC0 := zero_le_one.trans (majorArcCoverConstant_one_le n j hU hV)
  have hClog := majorArcCoverLog_nonneg n j hp hv
  have hL := (majorArcConstants_exp_bounds n (zero_le_one.trans hU) hp hUp).2.2.1
  have hL0 := (majorArcLengthConstant_pos n hU).le
  have hLlog := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hthree : (3 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
  have hbase := (mul_le_mul hthree hC hC0 (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hnum := pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) j le_rfl
  have hpowC := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (majorArcCoverExponent n j * j) le_rfl
  have hfirst := (mul_le_mul hnum hpowC (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hLt := pow_le_exp_mul_of_le_exp hL0 hL hLlog t le_rfl
  have hpowL := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (majorArcLengthExponent n * t) le_rfl
  have hsecond := mul_le_mul
    (mul_le_mul hWw hLt (pow_nonneg hL0 _) (Real.exp_pos _).le) hpowL (by positivity) (by positivity)
  simp only [← Real.exp_add] at hsecond
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ (j : ℝ) * (3 + majorArcCoverLog n j p v) +
      ((majorArcCoverExponent n j * j : ℕ) : ℝ) * uniformRetainedBiasLog n j t p v w E)
    (by positivity : 0 ≤ w + (t : ℝ) * majorArcLengthLog n p +
      ((majorArcLengthExponent n * t : ℕ) : ℝ) * uniformRetainedBiasLog n j t p v w E)
    hfirst hsecond
  have hplus := one_add_le_exp_succ (by positivity) hsum
  unfold uniformCharacterDenominatorBound
  simp only [div_eq_mul_inv]
  calc
    _ = 1 + ((3 * majorArcCoverConstant n j U V) ^ j * ζ⁻¹ ^ (majorArcCoverExponent n j * j) +
        W * majorArcLengthConstant n U ^ t * ζ⁻¹ ^ (majorArcLengthExponent n * t)) := by ring
    _ ≤ _ := hplus
    _ = _ := by unfold uniformRetainedDenominatorLog; congr 1; ring

end Erdos3

end

section

namespace Erdos3

theorem uniformScaledRetainedFrequencyBound_le (n d : ℕ) {U V ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    uniformScaledRetainedFrequencyBound n d U V ζ ≤
      2 * majorArcCoverConstant n d U V / ζ ^ majorArcCoverExponent n d := by
  have hX := one_le_inverse_power (majorArcCoverConstant_one_le n d hU hV) hζ hζ1
    (majorArcCoverExponent n d)
  have hc := Nat.ceil_lt_add_one (show 0 ≤ majorArcCoverConstant n d U V /
    ζ ^ majorArcCoverExponent n d by linarith)
  unfold uniformScaledRetainedFrequencyBound
  rw [mul_div_assoc]
  linarith

theorem uniformScaledRetainedDenominatorBound_le (n d t : ℕ) {U V W ζ : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) :
    uniformScaledRetainedDenominatorBound n d t U V W ζ ≤
      uniformCharacterDenominatorBound n d t U V W ζ := by
  have hX := one_le_inverse_power (majorArcCoverConstant_one_le n d hU hV) hζ hζ1
    (majorArcCoverExponent n d)
  have hf := uniformScaledRetainedFrequencyBound_le n d hU hV hζ hζ1
  rw [mul_div_assoc] at hf
  have hnonneg := uniformScaledRetainedFrequencyBound_nonneg n d U V ζ
  have hb : uniformScaledRetainedFrequencyBound n d U V ζ + 1 ≤
      3 * (majorArcCoverConstant n d U V / ζ ^ majorArcCoverExponent n d) := by linarith
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ uniformScaledRetainedFrequencyBound n d U V ζ + 1) hb d
  have he : (3 * (majorArcCoverConstant n d U V / ζ ^ majorArcCoverExponent n d)) ^ d =
      (3 * majorArcCoverConstant n d U V) ^ d / ζ ^ (majorArcCoverExponent n d * d) := by
    rw [← mul_div_assoc, div_pow, pow_mul]
  rw [he] at hp
  have hl : 0 ≤ W * majorArcLengthConstant n U ^ t / ζ ^ (majorArcLengthExponent n * t) :=
    div_nonneg (mul_nonneg hW (pow_nonneg (majorArcLengthConstant_pos n hU).le _)) (pow_pos hζ _).le
  have hn : 0 ≤ (3 * majorArcCoverConstant n d U V) ^ d / ζ ^ (majorArcCoverExponent n d * d) := by
    have := (majorArcCoverConstant_one_le n d hU hV)
    positivity
  unfold uniformScaledRetainedDenominatorBound uniformCharacterDenominatorBound
  exact max_le (by linarith) (by linarith)

theorem uniformScaledRetained_exp_bounds (n d t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    let ζ := uniformBlockRetainedBias n d t U V W ε
    uniformScaledRetainedFrequencyBound n d U V ζ ≤ Real.exp (uniformRetainedFrequencyLog n d t p v w E) ∧
    uniformScaledRetainedDenominatorBound n d t U V W ζ ≤ Real.exp (uniformRetainedDenominatorLog n d t p v w E) := by
  obtain ⟨hζ, hζ1, _⟩ := uniformBlockRetainedBias_spec n d t hU hW hε
  exact ⟨(uniformScaledRetainedFrequencyBound_le n d hU hV hζ hζ1).trans
      (uniformRetainedFrequency_exp_bound n d t hU hV hW hε hε1 hp hv hw hE hUp hVv hWw hεE),
    (uniformScaledRetainedDenominatorBound_le n d t hU hV hW hζ hζ1).trans
      (uniformCharacterDenominatorBound_exp_bound n d t hU hV hW hε hε1 hp hv hw hE hUp hVv hWw hεE)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PositiveRetainedDenominatorLog
namespace OAI

section

namespace Erdos3

theorem positiveModerateLengthConstant_exp_bound (n : ℕ) {U p : ℝ}
    (hU : 0 ≤ U) (hp : 0 ≤ p) (hUp : U ≤ Real.exp p) :
    positiveModerateLengthConstant n U ≤ Real.exp (positiveModerateLengthLog n p) := by
  have hn := (majorArcConstants_exp_bounds n hU hp hUp).2.2.1
  have hn1 := (majorArcConstants_exp_bounds (n + 1) hU hp hUp).2.2.1
  have hn0 := (majorArcBaseLogs_nonneg n hp).2.2.1
  have hn10 := (majorArcBaseLogs_nonneg (n + 1) hp).2.2.1
  have hfirst := one_add_le_exp_succ hn0 hn
  have hsum := add_le_exp_add_one (by positivity : 0 ≤ majorArcLengthLog n p + 1) hn10 hfirst hn1
  exact hsum.trans_eq (by unfold positiveModerateLengthLog; congr 1; ring)

theorem positiveModerateCoverConstant_exp_bound (n j : ℕ) {U V p v : ℝ}
    (hU : 0 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) :
    positiveModerateCoverConstant n j U V ≤ Real.exp (positiveModerateCoverLog n j p v) := by
  have hl := (majorArcConstants_exp_bounds (n + 1) hU hp hUp).2.2.1
  have hl0 := (majorArcBaseLogs_nonneg (n + 1) hp).2.2.1
  have hplus := one_add_le_exp_succ hl0 hl
  have hfour : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have h4V : 4 * V ≤ Real.exp (v + 4) :=
    (mul_le_mul hfour hVv hV (Real.exp_pos _).le).trans_eq
      (by rw [← Real.exp_add, add_comm])
  have hc := majorArcCoverConstant_exp_bound n j hU hp (by positivity : 0 ≤ v + 4) hUp h4V
  have hc1 := majorArcCoverConstant_exp_bound (n + 1) j hU hp hv hUp hVv
  have hcc : 0 ≤ majorArcCoverConstant n j U (4 * V) := by
    simp only [majorArcCoverConstant, majorArcBiasConstant, majorArcErrorConstant, majorArcLocalizationConstant]
    positivity
  have hprod := (mul_le_mul hplus hc hcc (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hc0 := majorArcCoverLog_nonneg n j hp (by positivity : 0 ≤ v + 4)
  have hc10 := majorArcCoverLog_nonneg (n + 1) j hp hv
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ majorArcLengthLog (n + 1) p + 1 + majorArcCoverLog n j p (v + 4))
    hc10 hprod hc1
  exact hsum

theorem positiveModerateSpectrumConstant_exp_bound (n j : ℕ) {U V p v : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) :
    positiveModerateSpectrumConstant n j U V ≤ Real.exp (positiveModerateSpectrumLog n j p v) := by
  have hc := positiveModerateCoverConstant_exp_bound n j (zero_le_one.trans hU) hV hp hv hUp hVv
  have hc0 := (positiveModerateCoverConstant_one_le n j hU hV).trans' zero_le_one
  have hlog := (positiveModerateLogs_nonneg n j 0 hp hv (le_refl (0 : ℝ))).2.1
  have hp4 := pow_le_exp_mul_of_le_exp hc0 hc hlog 4 le_rfl
  have h195 : (195 : ℝ) ≤ Real.exp 195 := by linarith [Real.add_one_le_exp (195 : ℝ)]
  have hbase := (mul_le_mul h195 hp4 (pow_nonneg hc0 _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  exact pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) j le_rfl

theorem positiveModerateAccuracyScale_exp_bound (n j t : ℕ) {U V W p v w : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w) :
    positiveModerateAccuracyScale n j t U V W ≤ Real.exp (positiveModerateAccuracyLog n j t p v w) := by
  have hlen := positiveModerateLengthConstant_exp_bound n (zero_le_one.trans hU) hp hUp
  have hspec := positiveModerateSpectrumConstant_exp_bound n j hU hV hp hv hUp hVv
  obtain ⟨hL, _, hS, _⟩ := positiveModerateLogs_nonneg n j t hp hv hw
  have hlen0 := (positiveModerateLengthConstant_pos n hU).le
  have hspec0 : 0 ≤ positiveModerateSpectrumConstant n j U V := by
    unfold positiveModerateSpectrumConstant
    positivity
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpowS : (2 : ℝ) ^ positiveModerateSpectrumExponent n j ≤
      Real.exp (positiveModerateSpectrumExponent n j : ℝ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (positiveModerateSpectrumExponent n j) le_rfl
  have hpowL : (2 : ℝ) ^ positiveModerateLengthExponent n ≤
      Real.exp (positiveModerateLengthExponent n : ℝ) := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo
      (by norm_num) (positiveModerateLengthExponent n) le_rfl
  have hfirst : 2 * positiveModerateSpectrumConstant n j U V * 2 ^ positiveModerateSpectrumExponent n j ≤
      Real.exp (1 + positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℝ)) := by
    have hh := mul_le_mul (mul_le_mul htwo hspec hspec0 (Real.exp_pos _).le) hpowS
      (by positivity) (by positivity)
    simpa only [← Real.exp_add] using hh
  have hbase := (mul_le_mul hpowL hlen hlen0 (Real.exp_pos _).le).trans_eq (Real.exp_add _ _).symm
  have hbasepow := pow_le_exp_mul_of_le_exp (by positivity) hbase (by positivity) t le_rfl
  have hsecond := (mul_le_mul hWw hbasepow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ 1 + positiveModerateSpectrumLog n j p v + (positiveModerateSpectrumExponent n j : ℝ))
    (by positivity : 0 ≤ w + (t : ℝ) * ((positiveModerateLengthExponent n : ℝ) + positiveModerateLengthLog n p))
    hfirst hsecond
  have hplus := one_add_le_exp_succ (by positivity) hsum
  exact hplus.trans_eq (by unfold positiveModerateAccuracyLog; congr 1; ring)

end Erdos3

end

section

namespace Erdos3

theorem positiveModerateRetainedBias_inverse_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    (positiveModerateRetainedBias n j t U V W ε)⁻¹ ≤
      Real.exp (positiveRetainedBiasLog n j t p v w E) := by
  have hA := positiveModerateAccuracyScale_exp_bound n j t hU hV hp hv hw hUp hVv hWw
  unfold positiveModerateRetainedBias positiveRetainedBiasLog
  rw [inv_div, div_eq_mul_inv]
  exact (mul_le_mul hA hεE (inv_nonneg.mpr hε.le) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm

theorem positiveModerateSpectrumCardBudget_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    positiveModerateSpectrumCardBudget n j t U V W ε ≤
      Real.exp (positiveSpectrumCardLog n j t p v w E) := by
  let ζ := positiveModerateRetainedBias n j t U V W ε
  have hζ : 0 ≤ ζ := div_nonneg hε.le
    (zero_le_one.trans (positiveModerateAccuracyScale_one_le n j t (V := V) hU hW))
  have hB := positiveModerateRetainedBias_inverse_exp_bound n j t hU hV hε hp hv hw
    hUp hVv hWw hεE
  have hB0 := (positiveRetainedLogs_nonneg n j t hp hv hw hE).1
  obtain ⟨hL0, _, hS0, _⟩ := positiveModerateLogs_nonneg n j t hp hv hw
  have hL := positiveModerateLengthConstant_exp_bound n (zero_le_one.trans hU) hp hUp
  have hLnonneg := (positiveModerateLengthConstant_pos n hU).le
  have hS := positiveModerateSpectrumConstant_exp_bound n j hU hV hp hv hUp hVv
  have hBS := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (positiveModerateSpectrumExponent n j) le_rfl
  have hBL := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (positiveModerateLengthExponent n * t) le_rfl
  have hLt := pow_le_exp_mul_of_le_exp hLnonneg hL hL0 t le_rfl
  have hfirst := (mul_le_mul hS hBS (pow_nonneg (inv_nonneg.mpr hζ) _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hsecond := mul_le_mul
    (mul_le_mul hWw hLt (pow_nonneg hLnonneg _) (Real.exp_pos _).le) hBL
    (pow_nonneg (inv_nonneg.mpr hζ) _) (by positivity)
  simp only [← Real.exp_add] at hsecond
  have hsum := add_le_exp_add_one
    (by positivity : 0 ≤ positiveModerateSpectrumLog n j p v +
      (positiveModerateSpectrumExponent n j : ℝ) * positiveRetainedBiasLog n j t p v w E)
    (by positivity : 0 ≤ w + (t : ℝ) * positiveModerateLengthLog n p +
      ((positiveModerateLengthExponent n * t : ℕ) : ℝ) * positiveRetainedBiasLog n j t p v w E)
    hfirst hsecond
  simpa only [positiveModerateSpectrumCardBudget, positiveSpectrumCardLog, div_eq_mul_inv, inv_pow] using hsum

theorem positiveRetainedFrequencyBound_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    positiveRetainedFrequencyBound n j U V (positiveModerateRetainedBias n j t U V W ε) ≤
      Real.exp (positiveRetainedFrequencyLog n j t p v w E) := by
  let ζ := positiveModerateRetainedBias n j t U V W ε
  have hζ : 0 ≤ ζ := div_nonneg hε.le
    (zero_le_one.trans (positiveModerateAccuracyScale_one_le n j t (V := V) hU hW))
  have hB := positiveModerateRetainedBias_inverse_exp_bound n j t hU hV hε hp hv hw
    hUp hVv hWw hεE
  have hB0 := (positiveRetainedLogs_nonneg n j t hp hv hw hE).1
  have hC := positiveModerateCoverConstant_exp_bound n j (zero_le_one.trans hU) hV hp hv hUp hVv
  have hC0 := (positiveModerateCoverConstant_one_le n j hU hV).trans' zero_le_one
  have hClog := (positiveModerateLogs_nonneg n j t hp hv hw).2.1
  have hpow := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (positiveModerateCoverExponent n j) le_rfl
  have hraw := (mul_le_mul hC hpow (pow_nonneg (inv_nonneg.mpr hζ) _) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hplus := one_add_le_exp_succ
    (by positivity : 0 ≤ positiveModerateCoverLog n j p v +
      (positiveModerateCoverExponent n j : ℝ) * positiveRetainedBiasLog n j t p v w E) hraw
  unfold positiveRetainedFrequencyBound
  calc
    _ ≤ positiveModerateCoverConstant n j U V / ζ ^ positiveModerateCoverExponent n j + 1 :=
      (Nat.ceil_lt_add_one (div_nonneg hC0 (pow_nonneg hζ _))).le
    _ ≤ Real.exp (positiveRetainedFrequencyLog n j t p v w E) := by
      simpa only [positiveRetainedFrequencyLog, div_eq_mul_inv, inv_pow, add_comm] using hplus

end Erdos3

end

section

namespace Erdos3

theorem positiveRetainedDenominatorBound_exp_bound (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    positiveRetainedDenominatorBound n j t U V W (positiveModerateRetainedBias n j t U V W ε) ≤
      Real.exp (positiveRetainedDenominatorLog n j t p v w E) := by
  let ζ := positiveModerateRetainedBias n j t U V W ε
  have hζ : 0 ≤ ζ := div_nonneg hε.le
    (zero_le_one.trans (positiveModerateAccuracyScale_one_le n j t (V := V) hU hW))
  obtain ⟨hB0, _, hF0⟩ := positiveRetainedLogs_nonneg n j t hp hv hw hE
  have hL0 := (positiveModerateLogs_nonneg n j t hp hv hw).1
  have hF := positiveRetainedFrequencyBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE
  have hf0 := positiveRetainedFrequencyBound_nonneg n j U V ζ
  have hplus : positiveRetainedFrequencyBound n j U V ζ + 1 ≤
      Real.exp (positiveRetainedFrequencyLog n j t p v w E + 1) := by
    simpa only [add_comm] using one_add_le_exp_succ hF0 hF
  have hfirst := pow_le_exp_mul_of_le_exp (by positivity) hplus (by positivity) j le_rfl
  have hB := positiveModerateRetainedBias_inverse_exp_bound n j t hU hV hε hp hv hw hUp hVv hWw hεE
  have hpow := pow_le_exp_mul_of_le_exp (inv_nonneg.mpr hζ) hB hB0
    (positiveModerateLengthExponent n * t) le_rfl
  have hL := positiveModerateLengthConstant_exp_bound n (zero_le_one.trans hU) hp hUp
  have hlen0 := (positiveModerateLengthConstant_pos n hU).le
  have hLt := pow_le_exp_mul_of_le_exp hlen0 hL hL0 t le_rfl
  have hsecond := mul_le_mul
    (mul_le_mul hWw hLt (pow_nonneg hlen0 _) (Real.exp_pos _).le) hpow (by positivity) (by positivity)
  simp only [← Real.exp_add] at hsecond
  have hleft0 : 0 ≤ (j : ℝ) * (positiveRetainedFrequencyLog n j t p v w E + 1) := by positivity
  have hright0 : 0 ≤ w + (t : ℝ) * positiveModerateLengthLog n p +
      ((positiveModerateLengthExponent n * t : ℕ) : ℝ) * positiveRetainedBiasLog n j t p v w E := by positivity
  unfold positiveRetainedDenominatorBound positiveRetainedDenominatorLog
  apply max_le
  · exact hfirst.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_right hright0))
  · have hb := hsecond.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hleft0))
    simpa only [div_eq_mul_inv, inv_pow] using hb

theorem positiveRetainedComplexity_exp_bounds (n j t : ℕ) {U V W ε p v w E : ℝ}
    (hU : 1 ≤ U) (hV : 0 ≤ V) (hW : 0 ≤ W) (hε : 0 < ε)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hE : 0 ≤ E)
    (hUp : U ≤ Real.exp p) (hVv : V ≤ Real.exp v) (hWw : W ≤ Real.exp w)
    (hεE : ε⁻¹ ≤ Real.exp E) :
    let ζ := positiveModerateRetainedBias n j t U V W ε
    let Q := positiveRetainedComplexityLog n j t p v w E
    positiveModerateSpectrumCardBudget n j t U V W ε ≤ Real.exp Q ∧
      positiveRetainedFrequencyBound n j U V ζ ≤ Real.exp Q ∧
      positiveRetainedDenominatorBound n j t U V W ζ ≤ Real.exp Q := by
  obtain ⟨_, hC, hF, hD⟩ := positiveRetainedComplexityLog_bounds n j t hp hv hw hE
  exact ⟨(positiveModerateSpectrumCardBudget_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hC),
    (positiveRetainedFrequencyBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hF),
    (positiveRetainedDenominatorBound_exp_bound n j t hU hV hW hε hp hv hw hE hUp hVv hWw hεE).trans
      (Real.exp_le_exp.mpr hD)⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AllocatedActiveBudgetedSite
namespace OAI

section

namespace Erdos3

theorem siteExponentialOutput_bounds (s k : ℕ) (hk : k ≤ s) {Q size period cap : ℝ}
    (hQ : 0 ≤ Q) (hsize : size ≤ Real.exp Q) (hperiod : period ≤ Real.exp Q)
    (hcap : cap ≤ Real.exp Q) :
    let O := siteExponentialOutputLog s Q
    size * Real.exp ((k : ℝ) * (4 * Q + 8)) ≤ Real.exp O ∧
      period ≤ Real.exp O ∧ cap * Real.exp ((k : ℝ) * (4 * Q + 8) + Q) ≤ Real.exp O ∧
      Real.exp (1 + 6 * Q + 12) + 4 ≤ Real.exp O ∧ Real.exp Q ≤ Real.exp O := by
  let N := (s : ℝ) * (4 * Q + 8)
  have hN : 0 ≤ N := by dsimp only [N]; positivity
  have hQO : Q ≤ siteExponentialOutputLog s Q := by
    change Q ≤ N + 8 * Q + 18
    linarith
  have hNO : N + 2 * Q ≤ siteExponentialOutputLog s Q := by
    change N + 2 * Q ≤ N + 8 * Q + 18
    linarith
  have hLO : 6 * Q + 18 ≤ siteExponentialOutputLog s Q := by
    change 6 * Q + 18 ≤ N + 8 * Q + 18
    linarith
  have hA : (k : ℝ) * (4 * Q + 8) ≤ N :=
    mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (by positivity)
  have hbase := Real.exp_le_exp.mpr hA
  have hbaseQ := Real.exp_le_exp.mpr (add_le_add hA (le_refl Q))
  have hT := (mul_le_mul hsize hbase (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hC := (mul_le_mul hcap hbaseQ (Real.exp_pos _).le (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hT' := hT.trans (Real.exp_le_exp.mpr
    (by linarith only [hNO, hQ] : Q + N ≤ siteExponentialOutputLog s Q))
  have hC' := hC.trans (Real.exp_le_exp.mpr
    (by linarith only [hNO] : Q + (N + Q) ≤ siteExponentialOutputLog s Q))
  have hL := add_le_exp_add_one (by positivity : 0 ≤ 1 + 6 * Q + 12)
    (by norm_num : (0 : ℝ) ≤ 4) (le_refl (Real.exp (1 + 6 * Q + 12)))
    (show (4 : ℝ) ≤ Real.exp 4 by linarith [Real.add_one_le_exp (4 : ℝ)])
  have hL' := hL.trans (Real.exp_le_exp.mpr
    (by linarith only [hLO] : (1 + 6 * Q + 12) + 4 + 1 ≤ siteExponentialOutputLog s Q))
  exact ⟨hT', hperiod.trans (Real.exp_le_exp.mpr hQO), hC', hL', Real.exp_le_exp.mpr hQO⟩

end Erdos3

end

section

namespace Erdos3

open scoped NNReal

theorem siteCharacterLipschitz_exp_bound (c r : ℕ) {D F f : ℝ}
    (hD : 0 ≤ D) (hF : 0 ≤ F) (hc : (c : ℝ) ≤ D) (hr : (r : ℝ) ≤ D)
    (hf : f ≤ Real.exp F) :
    (((CircleFourier.characterLipConstant * (r * Real.toNNReal f) + 4) *
      (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤ Real.exp (F + 2 * D + 13) := by
  have hfrequency : (Real.toNNReal f : ℝ) ≤ Real.exp F := coe_toNNReal_le_exp hf
  have hrow : (r : ℝ) ≤ Real.exp D := hr.trans (by linarith [Real.add_one_le_exp D])
  have hchar : (CircleFourier.characterLipConstant : ℝ) ≤ Real.exp 8 := by
    rw [CircleFourier.coe_characterLipConstant]
    linarith [Real.pi_lt_four, Real.add_one_le_exp (8 : ℝ)]
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hpow : (2 : ℝ) ^ c ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) c hc
  have hrowFreq := (mul_le_mul hrow hfrequency (Real.toNNReal f).coe_nonneg (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hprod := (mul_le_mul hchar hrowFreq (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have hplus := add_le_exp_add_one (by positivity : 0 ≤ 8 + (D + F))
    (by norm_num : (0 : ℝ) ≤ 4) hprod
    (show (4 : ℝ) ≤ Real.exp 4 by linarith [Real.add_one_le_exp (4 : ℝ)])
  have htotal := (mul_le_mul hplus hpow (by positivity) (Real.exp_pos _).le).trans_eq
    (Real.exp_add _ _).symm
  have htotal' : ((CircleFourier.characterLipConstant : ℝ) *
      ((r : ℝ) * (Real.toNNReal f : ℝ)) + 4) * (2 : ℝ) ^ c ≤ Real.exp (F + 2 * D + 13) :=
    htotal.trans_eq (by congr 1; ring)
  simpa only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_ofNat, NNReal.coe_pow] using htotal'

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedSupportedSlicedFullGridSite
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem boundedGridResources_exp_bound (c d K : ℕ) {D p : ℝ}
    (_hD : 0 ≤ D) (hp : 0 ≤ p) (hc : (c : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (hK : (K : ℝ) ≤ Real.exp p) :
    (K : ℝ) ^ d ≤ Real.exp (D * p) ∧
    (((d * (2 * (K : ℝ≥0) ^ 2) * (K : ℝ≥0) ^ d) * (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤
      Real.exp (2 * D + (D + 2) * p + 1) := by
  have hKd := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg K) hK hp d hd
  have hK2 := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg K) hK hp 2 le_rfl
  have ht : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have htc : (2 : ℝ) ^ c ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) ht (by norm_num) c hc
  have hdr : (d : ℝ) ≤ Real.exp D := hd.trans (by linarith [Real.add_one_le_exp D])
  have hprod := mul_le_mul
    (mul_le_mul (mul_le_mul hdr (mul_le_mul ht hK2 (by positivity) (Real.exp_nonneg _))
      (by positivity) (by positivity)) hKd (by positivity) (by positivity))
    htc (by positivity) (by positivity)
  simp only [← Real.exp_add] at hprod
  refine ⟨hKd, ?_⟩
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat]
  exact hprod.trans_eq (by congr 1; ring)

theorem slicedGridSite_numerics (c n d ta ti K : ℕ) {D p E U Va Vi Wa Wi ε R0 : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hc : (c : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (hU : 1 ≤ U) (hVa : 0 ≤ Va) (hVi : 0 ≤ Vi) (hWa : 0 ≤ Wa) (hWi : 0 ≤ Wi)
    (hUp : U ≤ Real.exp p) (hVap : Va ≤ Real.exp p) (hVip : Vi ≤ Real.exp p)
    (hWap : Wa ≤ Real.exp p) (hWip : Wi ≤ Real.exp p)
    (hKp : (K : ℝ) ≤ Real.exp p) (hRp : R0 + 1 / 4 ≤ Real.exp p)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hεE : ε⁻¹ ≤ Real.exp E) :
    let Q := slicedGridSiteLog n d ta ti D p E
    let ζa := positiveModerateRetainedBias n d ta U Va Wa ε
    let ζi := uniformBlockRetainedBias n d ti U Vi Wi ε
    let ca := positiveModerateSpectrumCardBudget n d ta U Va Wa 1 + 1
    let ci := uniformSpectrumAbsoluteCap n d ti U Vi Wi
    0 ≤ Q ∧ R0 + 1 / 4 ≤ Real.exp Q ∧
      (ε / (ca + 1))⁻¹ ≤ Real.exp Q ∧ (ε / (ci + 1))⁻¹ ≤ Real.exp Q ∧
      (((CircleFourier.characterLipConstant * (d * Real.toNNReal (positiveRetainedFrequencyBound n d U Va ζa)) + 4) *
        (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤ Real.exp Q ∧
      (((CircleFourier.characterLipConstant * (d * Real.toNNReal (uniformScaledRetainedFrequencyBound n d U Vi ζi)) + 4) *
        (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤ Real.exp Q ∧
      (K : ℝ) ^ d ≤ Real.exp Q ∧
      (((d * (2 * (K : ℝ≥0) ^ 2) * (K : ℝ≥0) ^ d) * (2 : ℝ≥0) ^ c : ℝ≥0) : ℝ) ≤ Real.exp Q ∧
      ε⁻¹ ≤ Real.exp Q ∧
      max 1 (max (positiveModerateSpectrumCardBudget n d ta U Va Wa ε)
        (uniformSpectrumSizeConstant n d ti U Vi Wi /
          ε ^ max (majorArcSpectrumExponent n d) (majorArcLengthExponent n * ti))) ≤ Real.exp Q ∧
      max 1 (max (positiveRetainedDenominatorBound n d ta U Va Wa ζa)
        (uniformScaledRetainedDenominatorBound n d ti U Vi Wi ζi)) ≤ Real.exp Q ∧
      max 1 (max ca ci) ≤ Real.exp Q := by
  intro Q ζa ζi ca ci
  obtain ⟨hQ, hpQ, hEQ, haQ, hsQ, hfQ, htQ, hcaQ, hciQ, hKQ, hKLQ⟩ :=
    slicedGridSiteLog_bounds n d ta ti hD hp hE
  obtain ⟨ha, haf, hat⟩ := positiveRetainedComplexity_exp_bounds n d ta hU hVa hWa hε
    hp hp hp hE hUp hVap hWap hεE
  have hi := uniformSpectrumCardBound_exp_bound n d ti hU hVi hWi hε hp hp hp hE hUp hVip hWip hεE
  obtain ⟨hif, hit⟩ := uniformScaledRetained_exp_bounds n d ti hU hVi hWi hε hε1
    hp hp hp hE hUp hVip hWip hεE
  have ha0 := positiveModerateSpectrumCardBudget_exp_bound n d ta hU hVa hWa zero_lt_one
    hp hp hp (le_refl (0 : ℝ)) hUp hVap hWap (by norm_num)
  have hi0 := uniformSpectrumAbsoluteCap_exp_bound n d ti hU hVi hWi hp hp hp hUp hVip hWip
  have halog := (positiveRetainedLogs_nonneg n d ta hp hp hp (le_refl (0 : ℝ))).2.1
  have hilog := (uniformSpectrumLogs_nonneg n d ti hp hp hp).2.2
  have hca : ca + 1 ≤ Real.exp (positiveSpectrumCardLog n d ta p p p 0 + 2) := by
    have h1 := one_add_le_exp_succ halog ha0
    have h2 := one_add_le_exp_succ (by linarith : 0 ≤ positiveSpectrumCardLog n d ta p p p 0 + 1) h1
    dsimp [ca]
    convert h2 using 1 <;> ring_nf
  have hci : ci + 1 ≤ Real.exp (uniformSpectrumSizeLog n d ti p p p + 2) := by
    have h1 := one_add_le_exp_succ (by linarith : 0 ≤ uniformSpectrumSizeLog n d ti p p p + 1) hi0
    dsimp [ci]
    convert h1 using 1 <;> ring_nf
  have hfrac {C b : ℝ} (hb : C + 1 ≤ Real.exp b) (hbQ : b + E ≤ Q) :
      (ε / (C + 1))⁻¹ ≤ Real.exp Q := by
    rw [inv_div, div_eq_mul_inv]
    exact ((mul_le_mul hb hεE (inv_nonneg.mpr hε.le) (Real.exp_nonneg _)).trans_eq
      (Real.exp_add _ _).symm).trans (Real.exp_le_exp.mpr hbQ)
  have halogE := (positiveRetainedComplexityLog_bounds n d ta hp hp hp hE).1
  have hiflog := (uniformRetainedLogs_nonneg n d ti hp hp hp hE).2.2.1
  have hLa := siteCharacterLipschitz_exp_bound c d hD halogE hc hd haf
  have hLi := siteCharacterLipschitz_exp_bound c d hD hiflog hc hd hif
  obtain ⟨hK, hKL⟩ := boundedGridResources_exp_bound c d K hD hp hc hd hKp
  have haQ' : positiveRetainedComplexityLog n d ta p p p E ≤ Q := by linarith
  have hcaQ' : positiveSpectrumCardLog n d ta p p p 0 + 2 ≤ Q := by linarith
  have hciQ' : uniformSpectrumSizeLog n d ti p p p + 2 ≤ Q := by linarith
  have h1 : (1 : ℝ) ≤ Real.exp Q := Real.one_le_exp_iff.mpr hQ
  refine ⟨hQ, hRp.trans (Real.exp_le_exp.mpr hpQ), hfrac hca hcaQ, hfrac hci hciQ,
    hLa.trans (Real.exp_le_exp.mpr haQ), hLi.trans (Real.exp_le_exp.mpr hfQ),
    hK.trans (Real.exp_le_exp.mpr hKQ), hKL.trans (Real.exp_le_exp.mpr hKLQ),
    hεE.trans (Real.exp_le_exp.mpr hEQ), ?_, ?_, ?_⟩
  · exact max_le h1 (max_le (ha.trans (Real.exp_le_exp.mpr haQ')) (hi.trans (Real.exp_le_exp.mpr hsQ)))
  · exact max_le h1 (max_le (hat.trans (Real.exp_le_exp.mpr haQ')) (hit.trans (Real.exp_le_exp.mpr htQ)))
  · exact max_le h1 (max_le ((le_add_of_nonneg_right zero_le_one).trans
      (hca.trans (Real.exp_le_exp.mpr hcaQ'))) ((le_add_of_nonneg_right zero_le_one).trans
      (hci.trans (Real.exp_le_exp.mpr hciQ'))))

theorem slicedGridPointCap_exp_bound (c n d ta ti K : ℕ) {D p U Va Vi Wa Wi : ℝ}
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hc : (c : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (hU : 1 ≤ U) (hVa : 0 ≤ Va) (hVi : 0 ≤ Vi) (hWa : 0 ≤ Wa) (hWi : 0 ≤ Wi)
    (hUp : U ≤ Real.exp p) (hVap : Va ≤ Real.exp p) (hVip : Vi ≤ Real.exp p)
    (hWap : Wa ≤ Real.exp p) (hWip : Wi ≤ Real.exp p) (hKp : (K : ℝ) ≤ Real.exp p) :
    max 1 (max ((K : ℝ) ^ d) (max (positiveModerateSpectrumCardBudget n d ta U Va Wa 1 + 1)
      (uniformSpectrumAbsoluteCap n d ti U Vi Wi))) ≤ Real.exp (slicedGridSiteLog n d ta ti D p 0) := by
  have hRp : (0 : ℝ) + 1 / 4 ≤ Real.exp p := by
    have := Real.one_le_exp_iff.mpr hp
    linarith
  obtain ⟨hQ, _, _, _, _, _, hK, _, _, _, _, hcap⟩ :=
    slicedGridSite_numerics c n d ta ti K hD hp (le_refl (0 : ℝ)) hc hd hU hVa hVi hWa hWi
      hUp hVap hVip hWap hWip hKp hRp zero_lt_one le_rfl (by norm_num : (1 : ℝ)⁻¹ ≤ Real.exp 0)
  exact max_le (Real.one_le_exp_iff.mpr hQ) (max_le hK ((le_max_right _ _).trans hcap))

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedFixedScalarCapBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial

open MeasureTheory
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
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option Empty → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := Empty) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

variable (Hchild : ℕ)

local notation "degree" => Fin.val j + 1
local notation "denom" => inactiveDenominator
  (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))
local notation "cost" => (denom : ℝ) * 2 ^ degree
local notation "torus" => blockTorusFactor (Fintype.card Empty) degree (Fintype.card (B (Sigma.mk j (Sum.inr i)))) 1

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in

theorem forecastInactive_sliced_fixed_zero_axis_geometry_bounds
    {δ D v w vq vchild : ℝ}
    (hD : 1 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvq : 0 ≤ vq) (hvc : 0 ≤ vchild)
    (hδ : 0 < δ) (hRj : 0 < R j)
    (hdegree : ((degree : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hqv : (q : ℝ) ≤ Real.exp vq)
    (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v) :
    let p := slicedFixedZeroGeometryLog D v w vq vchild
    ((torus : ℝ) * cost / δ ^ degree ≤ Real.exp p) ∧
    ((max (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i (Nat.ceil ((q : ℝ) / δ)))
      (denom * 2 ^ degree * Hchild ^ degree + 2 * denom) : ℕ) : ℝ) ≤ Real.exp p ∧
    (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) *
      R j + 1 / 4 ≤ Real.exp p := by
  intro p
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  let T : ℕ := Nat.ceil ((q : ℝ) / δ)
  let p0 := slicedGridGeometryLog D v w (vq + w + 1)
  let g := D + v + 8
  let pf := 2 * g + D * (vchild + 1) + 4
  have hp0 : 0 ≤ p0 := by dsimp [p0, slicedGridGeometryLog]; positivity
  have hpf : 0 ≤ pf := by dsimp [pf, g]; positivity
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hp0p : p0 ≤ p := by change p0 ≤ p0 + pf; linarith
  have hpfp : pf ≤ p := by change pf ≤ p0 + pf; linarith
  have hfrac : (q : ℝ) / δ ≤ Real.exp (vq + w) := by
    rw [div_eq_mul_inv]
    exact (mul_le_mul hqv hδw (inv_nonneg.mpr hδ.le) (Real.exp_nonneg _)).trans_eq
      (Real.exp_add _ _).symm
  have hT : (T : ℝ) ≤ Real.exp (vq + w + 1) :=
    natCeil_le_exp_succ (by positivity) (by positivity) hfrac
  obtain ⟨_, hV, _, _, hK, hsupport⟩ := allocatedSlicedGrid_geometry_bounds
    B R j i 0 1 T hD0 hv hw (by positivity) hδ hRj (by simpa using hD0) hdegree (by simpa using hD) htail hb
    hRv hRi hδw hT hcoeff
  have hslots : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hb
  have hγinv := (principalProfileSize_exp_bounds _ hRj hslots hRv hRi).2
  have hden := inactiveDenominator_le_exp (principalProfileSize_pos hRj _) hg hγinv
  have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hp2 : (2 : ℝ) ^ degree ≤ Real.exp D := by
    simpa only [mul_one] using pow_le_exp_mul_of_le_exp (by norm_num) htwo (by norm_num) degree hdegree
  have hpchild := pow_le_exp_mul_of_le_exp (Nat.cast_nonneg Hchild) hchild hvc degree hdegree
  have hfirst : (denom : ℝ) * 2 ^ degree * (Hchild : ℝ) ^ degree ≤
      Real.exp (g + 1 + D + D * vchild) := by
    have h := mul_le_mul (mul_le_mul hden hp2 (by positivity) (Real.exp_nonneg _))
      hpchild (by positivity) (by positivity)
    simpa only [← Real.exp_add] using h
  have hlast : (2 : ℝ) * denom ≤ Real.exp (g + 2) := by
    have h := mul_le_mul htwo hden (Nat.cast_nonneg _) (Real.exp_nonneg _)
    exact h.trans_eq (by rw [← Real.exp_add]; congr 1; ring)
  have hfixed : ((denom * 2 ^ degree * Hchild ^ degree + 2 * denom : ℕ) : ℝ) ≤ Real.exp pf := by
    have hsum := add_le_exp_add_one (by positivity) (by positivity) hfirst hlast
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    exact hsum.trans_eq (by congr 1; dsimp [pf]; ring)
  refine ⟨hV.trans (Real.exp_le_exp.mpr hp0p), ?_, ?_⟩
  · rw [Nat.cast_max]
    exact max_le (hK.trans (Real.exp_le_exp.mpr hp0p)) (hfixed.trans (Real.exp_le_exp.mpr hpfp))
  · simp only [Nat.cast_zero, pow_zero, zero_add, one_pow, one_mul, mul_one, Nat.cast_one] at hsupport
    exact hsupport.trans (Real.exp_le_exp.mpr hp0p)

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastInactiveSlicedCappedContinuousSource
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

theorem slicedGridSiteLog_le_uniform {m : ℕ} (j : Fin m) {p E : ℝ} (hp : 0 ≤ p) (hE : 0 ≤ E) :
    slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p E ≤ slicedFixedUniformSiteLog m p E := by
  have hs := Finset.single_le_sum (fun k (_ : k ∈ (Finset.univ : Finset (Fin m))) =>
    (slicedGridSiteLog_bounds k.val 1 (k.val + 1) (k.val + 1)
      (by norm_num : (0 : ℝ) ≤ 1) hp hE).1) (Finset.mem_univ j)
  unfold slicedFixedUniformSiteLog
  linarith

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R : Fin m → ℝ} {A : Type*} [Fintype A]

theorem forecastInactiveSlicedSiteNumerics_of_uniform_envelope
    (selected : A → Σ j : Fin m, Fin (n j)) (q Hchild : ℕ)
    (δ P δout D p E : ℝ) (hδ : 0 < δ) (hP : 1 ≤ P) (hδout : 0 < δout)
    (hD : 0 ≤ D) (hp : 0 ≤ p) (hE : 0 ≤ E)
    (hcard : (Fintype.card A : ℝ) ≤ D) (hPp : P ≤ Real.exp p)
    (hδoutE : δout⁻¹ ≤ Real.exp E) :
    let degree := fun a => (selected a).1.val + 1
    let denom := fun a => inactiveDenominator (principalProfileSize (R (selected a).1)
      (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
    let torus := fun a => blockTorusFactor (Fintype.card Empty) (degree a)
      (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
    let V := fun a => (torus a : ℝ) * ((denom a : ℝ) * 2 ^ degree a) / δ ^ degree a
    let cutoff := fun a => max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
      (selected a).1 (selected a).2 (Nat.ceil ((q : ℝ) / δ)))
      (denom a * 2 ^ degree a * Hchild ^ degree a + 2 * denom a)
    let R0 := fun a => (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) (degree a)) : ℝ) *
      R (selected a).1
    (∀ a, V a ≤ Real.exp p) → (∀ a, (cutoff a : ℝ) ≤ Real.exp p) →
    (∀ a, R0 a + 1 / 4 ≤ Real.exp p) →
    let Cactual := Real.exp (slicedFixedUniformSiteLog m p 0)
    let Eprod := slicedFixedUniformAccuracyLog m D p E
    let Q := slicedFixedUniformSiteLog m p Eprod
    let O := siteExponentialOutputLog 1 Q
    forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild δ P Cactual δout Q
      (Real.exp O) (Real.exp O) (Real.exp O) (Real.exp p) ⟨Real.exp O, Real.exp_nonneg _⟩ := by
  intro degree denom torus V cutoff R0 hVp hKp hRp Cactual Eprod Q O
  let cap a := uniformSpectrumAbsoluteCap (selected a).1.val 1 (degree a) P (V a) (V a)
  have hV (a : A) : 0 ≤ V a := by dsimp [V]; positivity
  have hcapLog : 0 ≤ slicedFixedUniformSiteLog m p 0 := slicedFixedUniformSiteLog_nonneg m hp le_rfl
  have hEprod : 0 ≤ Eprod := by
    dsimp [Eprod, slicedFixedUniformAccuracyLog]
    exact add_nonneg (uniformProductAccuracyLog_nonneg hD hcapLog hE) zero_le_one
  have hQ : 0 ≤ Q := slicedFixedUniformSiteLog_nonneg m hp hEprod
  have hactual (a : A) : max (cutoff a : ℝ) (cap a) ≤ Cactual := by
    have h := slicedGridPointCap_exp_bound 0 (selected a).1.val 1 (degree a) (degree a) (cutoff a)
      (by norm_num : (0 : ℝ) ≤ 1) hp (by norm_num) (by norm_num) hP (hV a) (hV a) (hV a) (hV a)
      hPp (hVp a) (hVp a) (hVp a) (hVp a) (hKp a)
    have hh : max (cutoff a : ℝ) (cap a) ≤ Real.exp
        (slicedGridSiteLog (selected a).1.val 1 (degree a) (degree a) 1 p 0) := by
      refine max_le ?_ ?_
      · simpa only [pow_one] using (le_max_left _ _).trans ((le_max_right _ _).trans h)
      · exact (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans h))
    exact hh.trans (Real.exp_le_exp.mpr (slicedGridSiteLog_le_uniform (selected a).1 hp le_rfl))
  let ε := uniformProductAccuracy (Fintype.card A) Cactual δout / 2
  obtain ⟨hτ, hτ1, _⟩ := uniformProductAccuracy_spec (Fintype.card A) (Real.exp_nonneg _) hδout
  have hε : 0 < ε := half_pos hτ
  have hε1 : ε ≤ 1 := by dsimp only [ε]; linarith
  have hεE : ε⁻¹ ≤ Real.exp Eprod := by
    have h := uniformProductAccuracy_inverse_exp_bound (Fintype.card A) (Real.exp_nonneg _) hδout
      hD hcapLog hE hcard (le_refl Cactual) hδoutE
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    dsimp only [ε]
    rw [inv_div, div_eq_mul_inv]
    exact (mul_le_mul htwo h (inv_nonneg.mpr hτ.le) (Real.exp_nonneg _)).trans_eq (by
      rw [← Real.exp_add]; congr 1; dsimp [Eprod, slicedFixedUniformAccuracyLog]; ring)
  have each (a : A) := slicedGridSite_numerics 0 (selected a).1.val 1 (degree a) (degree a) (cutoff a)
    (by norm_num : (0 : ℝ) ≤ 1) hp hEprod (by norm_num) (by norm_num) hP (hV a) (hV a) (hV a) (hV a)
    hPp (hVp a) (hVp a) (hVp a) (hVp a) (hKp a) (hRp a) hε hε1 hεE
  have hle (a : A) := Real.exp_le_exp.mpr (slicedGridSiteLog_le_uniform (selected a).1 hp hEprod)
  dsimp only [forecastInactiveSlicedSiteNumerics]
  refine ⟨hactual, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hRp⟩
  · intro a; exact (each a).2.1.trans (hle a)
  · intro a; exact (each a).2.2.2.1.trans (hle a)
  · intro a
    simpa only [Nat.cast_one, one_mul, pow_zero, mul_one] using (each a).2.2.2.2.2.1.trans (hle a)
  · intro a; simpa only [pow_one] using (each a).2.2.2.2.2.2.1.trans (hle a)
  · intro a
    simpa only [Nat.cast_one, one_mul, pow_one, pow_zero, mul_one] using
      (each a).2.2.2.2.2.2.2.1.trans (hle a)
  · apply hεE.trans
    apply Real.exp_le_exp.mpr
    have hs : 0 ≤ ∑ j : Fin m, slicedGridSiteLog j.val 1 (j.val + 1) (j.val + 1) 1 p Eprod :=
      Finset.sum_nonneg (fun j _ => (slicedGridSiteLog_bounds j.val 1 (j.val + 1) (j.val + 1)
        (by norm_num : (0 : ℝ) ≤ 1) hp hEprod).1)
    dsimp [Q, slicedFixedUniformSiteLog]
    linarith
  · intro a
    have hb := (le_max_right _ _).trans ((le_max_right _ _).trans (each a).2.2.2.2.2.2.2.2.2.1)
    have h1 := Real.one_le_exp_iff.mpr hQ
    obtain ⟨hT, _, _, _, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ (hb.trans (hle a)) h1 h1
    obtain ⟨hT1, _, _, _, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ h1 h1 h1
    exact max_le (by simpa only [Nat.cast_one, one_mul] using hT)
      (by simpa only [Nat.cast_one, one_mul, one_mul] using hT1)
  · intro a
    have hb := (le_max_right _ _).trans ((le_max_right _ _).trans (each a).2.2.2.2.2.2.2.2.2.2.1)
    have h1 := Real.one_le_exp_iff.mpr hQ
    obtain ⟨_, hper, _, _, he⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ h1 (hb.trans (hle a)) h1
    exact max_le hper (h1.trans he)
  · intro a
    have hb := (le_max_right _ _).trans ((le_max_right _ _).trans (each a).2.2.2.2.2.2.2.2.2.2.2)
    have h1 := Real.one_le_exp_iff.mpr hQ
    obtain ⟨_, _, hc, _, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ h1 h1 (hb.trans (hle a))
    obtain ⟨_, _, hc1, _, _⟩ := siteExponentialOutput_bounds 1 1 le_rfl hQ h1 h1 h1
    exact max_le (by simpa only [Nat.cast_one, one_mul] using hc)
      (by simpa only [Nat.cast_one, one_mul, one_mul] using hc1)
  · have h1 := Real.one_le_exp_iff.mpr hQ
    have hL := (siteExponentialOutput_bounds 1 1 le_rfl hQ h1 h1 h1).2.2.2.1
    exact_mod_cast hL

theorem forecastInactiveSlicedSiteNumerics_of_primitive_uniform_budgets
    (selected : A → Σ j : Fin m, Fin (n j)) (T Hchild : ℕ)
    (δ P δout D p E v w vq vchild : ℝ)
    (hδ : 0 < δ) (hP : 1 ≤ P) (hδout : 0 < δout) (hD : 1 ≤ D)
    (hp : 0 ≤ p) (hE : 0 ≤ E) (hv : 0 ≤ v) (hw : 0 ≤ w)
    (hvq : 0 ≤ vq) (hvc : 0 ≤ vchild)
    (hcard : (Fintype.card A : ℝ) ≤ D) (hPp : P ≤ Real.exp p)
    (hδoutE : δout⁻¹ ≤ Real.exp E) (hδw : δ⁻¹ ≤ Real.exp w)
    (hTv : (T : ℝ) ≤ Real.exp vq) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ a, 0 < R (selected a).1)
    (hdegree : ∀ a, (((selected a).1.val + 1 : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : ∀ a, (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤ D)
    (hRv : ∀ a, R (selected a).1 ≤ Real.exp v)
    (hRi : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp v)
    (hcoeff : ∀ a, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1)) : ℝ) ≤ Real.exp v) :
    let pAll := p + slicedFixedZeroGeometryLog D v w vq vchild
    let Cactual := Real.exp (slicedFixedUniformSiteLog m pAll 0)
    let Eprod := slicedFixedUniformAccuracyLog m D pAll E
    let Q := slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    0 ≤ Q ∧ 0 ≤ O ∧ ∀ q : ℕ, 0 < q → q ≤ T →
      forecastInactiveSlicedSiteNumerics (G := G) B (R := R) selected q Hchild δ P Cactual δout Q
        (Real.exp O) (Real.exp O) (Real.exp O) (Real.exp pAll) ⟨Real.exp O, Real.exp_nonneg _⟩ := by
  intro pAll Cactual Eprod Q O
  have hD0 := zero_le_one.trans hD
  have hg := slicedFixedZeroGeometryLog_nonneg hD0 hv hw hvq hvc
  have hpAll : 0 ≤ pAll := add_nonneg hp hg
  have hpLe : p ≤ pAll := le_add_of_nonneg_right hg
  have hgLe : slicedFixedZeroGeometryLog D v w vq vchild ≤ pAll := le_add_of_nonneg_left hp
  have hcapLog := slicedFixedUniformSiteLog_nonneg m hpAll (le_refl (0 : ℝ))
  have hEprod : 0 ≤ Eprod := by
    dsimp [Eprod, slicedFixedUniformAccuracyLog]
    exact add_nonneg (uniformProductAccuracyLog_nonneg hD0 hcapLog hE) zero_le_one
  have hQ := slicedFixedUniformSiteLog_nonneg m hpAll hEprod
  refine ⟨hQ, siteExponentialOutputLog_nonneg 1 hQ, ?_⟩
  intro q _ hqT
  have hqv : (q : ℝ) ≤ Real.exp vq := (Nat.cast_le.mpr hqT).trans hTv
  have hgeom (a : A) := forecastInactive_sliced_fixed_zero_axis_geometry_bounds
    (B := B) (R := R) (j := (selected a).1) (i := (selected a).2) (q := q) (Hchild := Hchild)
    hD hv hw hvq hvc hδ (hR a) (hdegree a) htail (hb a) (hRv a) (hRi a) hδw hqv hchild (hcoeff a)
  exact forecastInactiveSlicedSiteNumerics_of_uniform_envelope B selected q Hchild δ P δout D pAll E
    hδ hP hδout hD0 hpAll hE hcard (hPp.trans (Real.exp_le_exp.mpr hpLe)) hδoutE
    (fun a => (hgeom a).1.trans (Real.exp_le_exp.mpr hgLe))
    (fun a => (hgeom a).2.1.trans (Real.exp_le_exp.mpr hgLe))
    (fun a => (hgeom a).2.2.trans (Real.exp_le_exp.mpr hgLe))

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable {R : Fin m → ℝ} {A : Type*} [Fintype A]

theorem forecastInactiveSlicedTailCap_of_primitive_uniform_budgets
    (selected : A → Σ j : Fin m, Fin (n j)) (Hchild : ℕ)
    (δ P D p v w vchild : ℝ)
    (hδ : 0 < δ) (hP : 1 ≤ P) (hD : 1 ≤ D)
    (hp : 0 ≤ p) (hv : 0 ≤ v) (hw : 0 ≤ w) (hvc : 0 ≤ vchild)
    (hcard : (Fintype.card A : ℝ) ≤ D) (hPp : P ≤ Real.exp p)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ a, 0 < R (selected a).1)
    (hdegree : ∀ a, (((selected a).1.val + 1 : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : ∀ a, (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤ D)
    (hRv : ∀ a, R (selected a).1 ≤ Real.exp v)
    (hRi : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp v)
    (hcoeff : ∀ a, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1)) : ℝ) ≤ Real.exp v) :
    let Ctail := Real.exp (slicedFixedUniformSiteLog m
      (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0)
    ∀ a,
      let degree := (selected a).1.val + 1
      let denom := inactiveDenominator (principalProfileSize (R (selected a).1)
        (Finset.card (layerIntegerPrincipalSlots (G := G) B (selected a).1 (selected a).2)))
      let torus := blockTorusFactor (Fintype.card Empty) degree
        (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩)) 1
      let V := (torus : ℝ) * ((denom : ℝ) * 2 ^ degree) / δ ^ degree
      let cutoff := max (allocatedSlicedGridHeightCutoff (G := G) B (R := R)
        (selected a).1 (selected a).2 (Nat.ceil ((1 : ℝ) / δ)))
        (denom * 2 ^ degree * Hchild ^ degree + 2 * denom)
      max (cutoff : ℝ)
        (uniformSpectrumAbsoluteCap (selected a).1.val 1 degree P V V) ≤ Ctail := by
  have hnum := forecastInactiveSlicedSiteNumerics_of_primitive_uniform_budgets
    B selected 1 Hchild δ P 1 D p 0 v w 0 vchild
    hδ hP (by norm_num) hD hp (le_refl 0) hv hw (le_refl 0) hvc hcard hPp
    (by simp) hδw (by simp) hchild hR hdegree htail hb hRv hRi hcoeff
  simpa only [Nat.cast_one] using (hnum.2.2 1 (by norm_num) le_rfl).1

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.ForecastSlicedPrimitiveCutoffBudget
namespace OAI

section

namespace Erdos3
open scoped NNReal

theorem exists_forecast_sliced_early_approximation_budget (m Dmod d : ℕ)
    {D ptail psite v w vchild Psm Plip Pbad Ppres E Pspatial Pcoord Pcut : ℝ}
    (hD : 0 ≤ D) (htail : 0 ≤ ptail) (hsite : 0 ≤ psite)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hchild : 0 ≤ vchild)
    (hsm : 0 ≤ Psm) (hlip : 0 ≤ Plip) (hbad : 0 ≤ Pbad)
    (hpres : 0 ≤ Ppres) (hE : 0 ≤ E) (hspatial : 0 ≤ Pspatial)
    (hcoord : 0 ≤ Pcoord) (hcut : 0 ≤ Pcut) :
    let pTailAll := ptail + VectorPolynomial.slicedFixedZeroGeometryLog D v w 0 vchild
    let tailLog := VectorPolynomial.slicedFixedUniformSiteLog m pTailAll 0
    let Pin := D * tailLog
    let Pdec := (Pbad + Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + Psm) + 3
    let Esite := E + Psm + 1 + d * V
    let pAll := psite + VectorPolynomial.slicedFixedZeroGeometryLog D v w V vchild
    let Eprod := VectorPolynomial.slicedFixedUniformAccuracyLog m D pAll Esite
    let Q := VectorPolynomial.slicedFixedUniformSiteLog m pAll Eprod
    let O := siteExponentialOutputLog 1 Q
    let Pperiod := V + D * O
    let Pfactor := Plip + D + O + 1 + Pspatial
    let Pnative := Pperiod + Pfactor + Pcoord + Pcut + 1
    let Pmass := Psm + d * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    0 ≤ Pin ∧ 0 ≤ V ∧ 0 ≤ Esite ∧ 0 ≤ pAll ∧ 0 ≤ Q ∧ 0 ≤ O ∧ 0 ≤ Pnative ∧
    (∀ a : ℕ, (a : ℝ) ≤ D → (Real.exp tailLog) ^ a ≤ Real.exp Pin) ∧
    ∃ (T : ℕ) (δ : ℝ), 0 < T ∧ (T : ℝ) ≤ Real.exp V ∧
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp Esite ∧
      (∀ (Rbad Qpres : ℕ) (H I : ℝ),
        0 ≤ H → H ≤ Real.exp Psm → I ≤ Real.exp Pin →
        (Rbad : ℝ) ≤ Real.exp Pbad → (Qpres : ℝ) ≤ Real.exp Ppres →
        H * (I * ((((Rbad * Qpres : ℕ) : ℝ) ^
          (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
            modularRankChargeFactor m)) / T) + (T : ℝ) ^ d * δ) ≤ Real.exp (-E)) ∧
      (∀ (H C : ℝ), 0 ≤ H → H ≤ Real.exp Psm → 0 ≤ C → C ≤ Real.exp Pdec →
        H * Real.exp Pin * (1 + C) ≤ Real.exp Pcap) ∧
      (∀ (a : ℕ) (H : ℝ), (a : ℝ) ≤ D → 0 ≤ H → H ≤ Real.exp Psm →
        2 * H * ((T : ℝ) ^ d * Real.exp (a * O)) ≤ Real.exp Pmass) ∧
      (∀ (a : ℕ) (q : ℕ) (L Lsp : ℝ≥0), (a : ℝ) ≤ D →
        (q : ℝ) ≤ Real.exp (V + a * O) → (L : ℝ) ≤ Real.exp Plip →
        (Lsp : ℝ) ≤ Real.exp Pspatial →
        (q : ℝ) ≤ Real.exp Pnative ∧
        (((L + a * ⟨Real.exp O, Real.exp_nonneg _⟩) * Lsp : ℝ≥0) : ℝ) ≤
          Real.exp Pnative) ∧
      Real.exp Pcoord ≤ Real.exp Pnative ∧ Real.exp Pcut ≤ Real.exp Pnative ∧
      (∀ H I C : ℝ, 0 ≤ H → 0 ≤ C → H ≤ Real.exp Psm → I ≤ Real.exp Pin →
        C ≤ Real.exp Pdec →
        H * (I * (C / T) + (T : ℝ) ^ d * δ) ≤ Real.exp (-E)) := by
  intro pTailAll tailLog Pin Pdec V Esite pAll Eprod Q O Pperiod Pfactor Pnative Pmass Pcap
  have htailAll : 0 ≤ pTailAll := add_nonneg htail
    (VectorPolynomial.slicedFixedZeroGeometryLog_nonneg hD hv hw (le_refl 0) hchild)
  have htailLog : 0 ≤ tailLog := VectorPolynomial.slicedFixedUniformSiteLog_nonneg m htailAll (le_refl 0)
  have hPin : 0 ≤ Pin := mul_nonneg hD htailLog
  have hPdec : 0 ≤ Pdec := by dsimp only [Pdec]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have hEs : 0 ≤ Esite := by dsimp only [Esite]; positivity
  have hpAll : 0 ≤ pAll := add_nonneg hsite
    (VectorPolynomial.slicedFixedZeroGeometryLog_nonneg hD hv hw hV hchild)
  have hcap : 0 ≤ VectorPolynomial.slicedFixedUniformSiteLog m pAll 0 :=
    VectorPolynomial.slicedFixedUniformSiteLog_nonneg m hpAll (le_refl 0)
  have hprod : 0 ≤ Eprod := add_nonneg
    (uniformProductAccuracyLog_nonneg hD hcap hEs) zero_le_one
  have hQ : 0 ≤ Q := VectorPolynomial.slicedFixedUniformSiteLog_nonneg m hpAll hprod
  have hO : 0 ≤ O := siteExponentialOutputLog_nonneg 1 hQ
  have hperiod : 0 ≤ Pperiod := add_nonneg hV (mul_nonneg hD hO)
  have hfactor : 0 ≤ Pfactor := by dsimp only [Pfactor]; positivity
  have hn : 0 ≤ Pnative := by dsimp only [Pnative]; positivity
  obtain ⟨T, δ, hT, hTv, hδ, hδ1, hδb, heRaw⟩ :=
    exists_forecast_weighted_approximation_parameters d hsm hPin hPdec hE
  have he := fun (Rbad Qpres : ℕ) (H I : ℝ) (hH : 0 ≤ H)
      (hHb : H ≤ Real.exp Psm) (hIb : I ≤ Real.exp Pin)
      (hR : (Rbad : ℝ) ≤ Real.exp Pbad) (hQp : (Qpres : ℝ) ≤ Real.exp Ppres) =>
    heRaw H I _ hH (Real.rpow_nonneg (Nat.cast_nonneg _) _) hHb hIb
      (forecastModularCharge_exp_bound m Dmod Rbad Qpres hR hQp)
  refine ⟨hPin, hV, hEs, hpAll, hQ, hO, hn, ?_, T, δ, hT, hTv, hδ, hδ1, hδb, he, ?_, ?_, ?_, ?_, ?_, heRaw⟩
  · intro a ha
    rw [← Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha htailLog)
  · intro H C hH hHb hC hCb
    have hsum : 1 + C ≤ 2 * Real.exp Pdec := by
      have h1 := Real.one_le_exp_iff.mpr hPdec
      linarith
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp Psm * Real.exp Pin * (2 * Real.exp Pdec) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hHb (Real.exp_nonneg _)) hsum
          (by positivity) (by positivity)
      _ ≤ Real.exp Psm * Real.exp Pin * (Real.exp 1 * Real.exp Pdec) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)) (by positivity)
      _ = Real.exp Pcap := by simp only [Pcap, Real.exp_add]; ring
  · intro a H ha hH hHb
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg T) hTv d
    have hao : Real.exp ((a : ℝ) * O) ≤ Real.exp (D * O) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ha hO)
    have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * Real.exp Psm * ((Real.exp V) ^ d * Real.exp (D * O)) :=
        mul_le_mul (mul_le_mul htwo hHb hH (Real.exp_nonneg _))
          (mul_le_mul hp hao (Real.exp_nonneg _) (by positivity)) (by positivity) (by positivity)
      _ = Real.exp Pmass := by rw [← Real.exp_nat_mul]; simp only [Pmass, Real.exp_add]; ring
  · intro a q L Lsp ha hq hL hLsp
    have hpq : V + a * O ≤ Pperiod := by
      dsimp only [Pperiod]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right ha hO)
    have hpN : Pperiod ≤ Pnative := by dsimp only [Pnative]; linarith
    refine ⟨hq.trans (Real.exp_le_exp.mpr (hpq.trans hpN)), ?_⟩
    have haexp : (a : ℝ) ≤ Real.exp D := ha.trans (by linarith [Real.add_one_le_exp D])
    have hsum : (L : ℝ) + a * Real.exp O ≤ Real.exp (Plip + D + O + 1) := by
      have h1 : (L : ℝ) ≤ Real.exp (Plip + D + O) :=
        hL.trans (Real.exp_le_exp.mpr (by linarith))
      have h2 : (a : ℝ) * Real.exp O ≤ Real.exp (Plip + D + O) := by
        calc
          _ ≤ Real.exp D * Real.exp O := mul_le_mul_of_nonneg_right haexp (Real.exp_nonneg _)
          _ = Real.exp (D + O) := (Real.exp_add _ _).symm
          _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
      have htwo : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc
        _ ≤ 2 * Real.exp (Plip + D + O) := by linarith
        _ ≤ Real.exp 1 * Real.exp (Plip + D + O) :=
          mul_le_mul_of_nonneg_right htwo (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hfactorN : Pfactor ≤ Pnative := by dsimp only [Pnative]; linarith
    simp only [NNReal.coe_mul, NNReal.coe_add]
    calc
      _ ≤ Real.exp (Plip + D + O + 1) * Real.exp Pspatial :=
        mul_le_mul hsum hLsp (NNReal.coe_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp Pfactor := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr hfactorN
  · apply Real.exp_le_exp.mpr
    dsimp only [Pnative]
    linarith
  · apply Real.exp_le_exp.mpr
    dsimp only [Pnative]
    linarith

end Erdos3

end

section

namespace Erdos3
open scoped NNReal

theorem forecastSlicedPrimitiveEnvelope_mul_cutoff
    (L : ℝ≥0) {Ptail p V : ℝ} {T : ℕ}
    (hT : 0 < T) (hP : 1 ≤ Ptail)
    (htail : scalarCubePrimitiveEnvelope Empty L 1 0 1 ≤ Ptail)
    (hPexp : Ptail ≤ Real.exp p) (hTexp : (T : ℝ) ≤ Real.exp V) :
    1 ≤ Ptail * T ∧
      scalarCubePrimitiveEnvelope Empty L 1 0 T ≤ Ptail * T ∧
      Ptail * T ≤ Real.exp (p + V) ∧
      ∀ s : ℕ, (s : ℝ) ≤ Ptail → ((s * T : ℕ) : ℝ) ≤ Ptail * T := by
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast (Nat.succ_le_of_lt hT)
  refine ⟨one_le_mul_of_one_le_of_one_le hP hT1, ?_, ?_, ?_⟩
  · have h := scalarCubePrimitiveEnvelope_le_scaled Empty L 1 0 (Nat.succ_le_of_lt hT)
    simpa only [Fintype.card_empty, zero_add, pow_one] using
      h.trans (mul_le_mul_of_nonneg_right htail (by positivity))
  · rw [Real.exp_add]
    exact mul_le_mul hPexp hTexp (Nat.cast_nonneg _) (Real.exp_nonneg _)
  · intro s hs
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hs (Nat.cast_nonneg _)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PreparedActualSlicedForecastSetup
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators Classical NNReal Matrix

variable {m : ℕ} {G : Type} [Fintype G]
variable {I : Fin m → Type} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable {B : LayerSamplerAxis I n → Type} [∀ a, Fintype (B a)]
variable {J : Fin m → Type} [∀ j, Fintype (J j)]
variable {U : ∀ j, Submodule ℝ (J j → ℝ)}
variable {b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ}
variable {R σ : Fin m → ℝ} {S : LayerSamplerScale (G := G) B U b R σ}
variable {X : Type} [Fintype X] [DecidableEq X]
variable {Eout : Fin m → Type} [∀ j, Fintype (Eout j)]
variable {A : Type} [Fintype A]
variable {Dmod : ℕ} {selected : A → Σ j : Fin m, Fin (n j)}
variable {τ δslice : ℝ}

variable (s : ActualFixedSpatialForecastSetup (X := X) (Eout := Eout)
  B U b S Dmod selected τ δslice)

theorem exists_actualFixedSpatialSlicedForecastNumerics_s2_oai
    (δ : ℝ) (Hchild : ℕ) (kernelV Ptail D p v w vchild E Pspatial Pcoord Pcut : ℝ)
    (hδ : 0 < δ) (hk : 0 ≤ kernelV) (hPtail : 1 ≤ Ptail)
    (hprimitive : s.Pcap ≤ Ptail) (hD : 1 ≤ D) (hp : 0 ≤ p)
    (hv : 0 ≤ v) (hw : 0 ≤ w) (hvc : 0 ≤ vchild) (hE : 0 ≤ E)
    (hsp : 0 ≤ Pspatial) (hco : 0 ≤ Pcoord) (hcu : 0 ≤ Pcut)
    (hcard : (Fintype.card A : ℝ) ≤ D) (hPp : Ptail ≤ Real.exp p)
    (hδw : δ⁻¹ ≤ Real.exp w) (hchild : (Hchild : ℝ) ≤ Real.exp vchild)
    (hR : ∀ a, 0 < R (selected a).1)
    (hdegree : ∀ a, (((selected a).1.val + 1 : ℕ) : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : ∀ a, (Fintype.card (B ⟨(selected a).1, Sum.inr (selected a).2⟩) : ℝ) ≤ D)
    (hRv : ∀ a, R (selected a).1 ≤ Real.exp v)
    (hRi : ∀ a, (R (selected a).1)⁻¹ ≤ Real.exp v)
    (hcoeff : ∀ a, (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B)
      ((selected a).1.val + 1)) : ℝ) ≤ Real.exp v)
    (hspatial : max (8 / τ) 1 ≤ Real.exp Pspatial)
    (hcoord : ((s.K * ∑ j, s.forward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp Pcoord)
    (hcut : (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound /
      (2 * s.radius)) * (s.K * ∑ j, s.forward j * Fintype.card (J j)) : ℝ≥0) : ℝ) ≤ Real.exp Pcut) :
    let Psm := forecastOriginalSmoothBudget m (s.P + (Fintype.card X + 1) * kernelV)
    let tailLog := slicedFixedUniformSiteLog m (p + slicedFixedZeroGeometryLog D v w 0 vchild) 0
    let Pin := D * tailLog
    let Pdec := (s.Pbad + s.Ppres) * ((Dmod + 2 : ℕ) : ℝ) * modularRankChargeFactor m
    let V := Pin + Pdec + (E + s.Pκ + Psm) + 3
    let Esite := E + s.Pκ + Psm + 1 + ((Dmod + 1 : ℕ) : ℝ) * V
    let pAll := p + V + slicedFixedZeroGeometryLog D v w V vchild
    let Q := slicedFixedUniformSiteLog m pAll (slicedFixedUniformAccuracyLog m D pAll Esite)
    let O := siteExponentialOutputLog 1 Q
    let Pnative := (V + D * O) + (Psm + D + O + 1 + Pspatial) + Pcoord + Pcut + 1
    let Pmass := Psm + ((Dmod + 1 : ℕ) : ℝ) * V + D * O + 1
    let Pcap := Psm + Pin + Pdec + 1
    ∃ nu : ActualFixedSpatialSlicedForecastNumerics s,
      nu.δ = δ ∧ nu.Hchild = Hchild ∧ nu.v = kernelV ∧ nu.Ptail = Ptail ∧ nu.E = E ∧
      nu.Pnative = Pnative ∧ nu.massLog = s.Pκ + Pmass ∧ nu.capLog = s.Pκ + Pcap ∧
      nu.Ctail = Real.exp tailLog ∧ (nu.T : ℝ) ≤ Real.exp V ∧
      0 ≤ nu.massLog ∧ 0 ≤ nu.capLog := by
  let _ : DecidableEq X := inferInstance
  intro Psm tailLog Pin Pdec V Esite pAll Q O Pnative Pmass Pcap
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hPs : 0 ≤ s.P := zero_le_one.trans s.hP
  have hBad := s.hPbad
  have hPres := s.hPpres
  have hsm : 0 ≤ Psm := (forecastOriginalSmoothBudget_bounds m (by positivity)).1
  have hEtotal : 0 ≤ E + s.Pκ := add_nonneg hE s.hPκ
  have htailLog : 0 ≤ tailLog := slicedFixedUniformSiteLog_nonneg m
    (add_nonneg hp (slicedFixedZeroGeometryLog_nonneg hD0 hv hw (le_refl 0) hvc)) (le_refl 0)
  have hPin : 0 ≤ Pin := mul_nonneg hD0 htailLog
  have hPdec : 0 ≤ Pdec := by dsimp [Pdec]; positivity
  have hV : 0 ≤ V := by dsimp [V]; positivity
  obtain ⟨_, _, hEs, hpAll, hQ, hO, hN, htailBound, T, δout, hT, hTv,
      hδout, hδout1, hδoutE, _, hcapBound, hmassBound, hfactorBound, hcoordBound,
      hcutBound, herrorBound⟩ :=
    exists_forecast_sliced_early_approximation_budget m Dmod (Dmod + 1)
      hD0 hp (add_nonneg hp hV) hv hw hvc hsm hsm s.hPbad s.hPpres hEtotal hsp hco hcu
  have hPsite := forecastSlicedPrimitiveEnvelope_mul_cutoff s.L hT hPtail
    (s.hprimitiveCap.trans hprimitive) hPp hTv
  have hnum := forecastInactiveSlicedSiteNumerics_of_primitive_uniform_budgets
    B selected T Hchild δ (Ptail * T) δout D (p + V) Esite v w V vchild
    hδ hPsite.1 hδout hD (add_nonneg hp hV) hEs hv hw hV hvc hcard hPsite.2.2.1
    hδoutE hδw hTv hchild hR hdegree htail hb hRv hRi hcoeff
  have htailActual := forecastInactiveSlicedTailCap_of_primitive_uniform_budgets
    B selected Hchild δ Ptail D p v w vchild hδ hPtail hD hp hv hw hvc hcard hPp
    hδw hchild hR hdegree htail hb hRv hRi hcoeff
  have hI : (Real.exp tailLog) ^ Fintype.card A ≤ Real.exp Pin := htailBound _ hcard
  have hperiod : (T : ℝ) * (Real.exp O) ^ Fintype.card A ≤ Real.exp Pnative := by
    have hao : (Fintype.card A : ℝ) * O ≤ D * O := mul_le_mul_of_nonneg_right hcard hO
    calc
      _ ≤ Real.exp V * (Real.exp O) ^ Fintype.card A :=
        mul_le_mul_of_nonneg_right hTv (by positivity)
      _ = Real.exp (V + (Fintype.card A : ℝ) * O) := by
        rw [← Real.exp_nat_mul]
        exact (Real.exp_add V _).symm
      _ ≤ Real.exp Pnative := Real.exp_le_exp.mpr (by dsimp [Pnative]; linarith)
  let Hbudget : ℝ := actualSlicedForecastDensityBudget s kernelV
  have hHb : Hbudget = Real.exp Psm := rfl
  have hH : 0 ≤ Hbudget := by rw [hHb]; positivity
  let Lsp : ℝ≥0 := ⟨max (8 / τ) 1, le_trans zero_le_one (le_max_right _ _)⟩
  have hfac := (hfactorBound (Fintype.card A) 0 ⟨Hbudget, hH⟩ Lsp hcard
    (by simpa only [Nat.cast_zero] using Real.exp_nonneg _) (le_of_eq hHb) hspatial).2
  change (Hbudget + (Fintype.card A : ℝ) * Real.exp O) * max (8 / τ) 1 ≤ Real.exp Pnative at hfac
  have hm := hmassBound (Fintype.card A) Hbudget hcard hH (le_of_eq hHb)
  have he := herrorBound Hbudget ((Real.exp tailLog) ^ Fintype.card A) (Real.exp Pdec)
    hH (Real.exp_nonneg _) (le_of_eq hHb) hI le_rfl
  have hc := hcapBound Hbudget (Real.exp Pdec) hH (le_of_eq hHb) (Real.exp_nonneg _) le_rfl
  let nu : ActualFixedSpatialSlicedForecastNumerics s := {
    T := T, hT := hT, δ := δ, hδ := hδ, Hchild := Hchild, v := kernelV, hv := hk,
    Ptail := Ptail, Ctail := Real.exp tailLog, hPtail := hPtail, hprimitive := hprimitive,
    hCtail := Real.exp_nonneg _, Cactual := Real.exp (slicedFixedUniformSiteLog m pAll 0),
    δout := δout, Q := Q, Nt := Real.exp O, Vt := Real.exp O, Ct := Real.exp O,
    Ht := Real.exp pAll, Lt := ⟨Real.exp O, Real.exp_nonneg _⟩,
    hCactual := Real.exp_nonneg _, hδout := hδout, hQ := hQ, hCt := Real.exp_nonneg _,
    hnumerics := hnum.2.2, htailactual := htailActual,
    Pnative := Pnative, massLog := s.Pκ + Pmass, capLog := s.Pκ + Pcap, E := E,
    hPnative := hN, hperiod := hperiod,
    hfactor := hfac,
    hcoord := hcoord.trans hcoordBound, hcut := hcut.trans hcutBound,
    hmass := by
      have hm' : 2 * Hbudget * ((T : ℝ) ^ (Dmod + 1) * (Real.exp O) ^ Fintype.card A) ≤ Real.exp Pmass := by
        simpa only [Real.exp_nat_mul] using hm
      calc
        _ ≤ Real.exp s.Pκ * Real.exp Pmass :=
          mul_le_mul s.hκcap hm' (by positivity) (Real.exp_nonneg _)
        _ = _ := (Real.exp_add _ _).symm,
    herror := by
      change s.κ * (Hbudget * ((Real.exp tailLog) ^ Fintype.card A * (Real.exp Pdec / T) +
        (T : ℝ) ^ (Dmod + 1) * δout)) ≤ Real.exp (-E)
      calc
        _ ≤ Real.exp s.Pκ * Real.exp (-(E + s.Pκ)) :=
          mul_le_mul s.hκcap he (by positivity) (Real.exp_nonneg _)
        _ = _ := by rw [← Real.exp_add]; congr 1; ring,
    hcap := by
      change s.κ * Hbudget * (Real.exp tailLog) ^ Fintype.card A * (1 + Real.exp Pdec) ≤ _
      have hi := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hI hH) (by positivity : 0 ≤ 1 + Real.exp Pdec)
      calc
        _ = s.κ * (Hbudget * (Real.exp tailLog) ^ Fintype.card A * (1 + Real.exp Pdec)) := by ring
        _ ≤ Real.exp s.Pκ * Real.exp Pcap :=
          mul_le_mul s.hκcap (hi.trans hc) (by positivity) (Real.exp_nonneg _)
        _ = _ := (Real.exp_add _ _).symm }
  refine ⟨nu, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hTv, ?_, ?_⟩
  · change 0 ≤ s.Pκ + Pmass
    have hκ := s.hPκ
    dsimp only [Pmass]
    positivity
  · change 0 ≤ s.Pκ + Pcap
    have hκ := s.hPκ
    dsimp only [Pcap]
    positivity

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution : type_of% @OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecastNumerics_s2_oai := @OAI.Erdos3.VectorPolynomial.exists_actualFixedSpatialSlicedForecastNumerics_s2_oai
