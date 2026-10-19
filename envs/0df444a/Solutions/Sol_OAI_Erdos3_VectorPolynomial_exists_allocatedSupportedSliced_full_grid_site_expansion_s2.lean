-- Prove2me | solution 1 for OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_full_grid_site_expansion_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T06:08:06.71413+00:00
-- url     : https://prove2.me/submissions/62cf5646-60ae-4128-83dd-ba160a43e2a3

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B217
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedFullGridNaturalSite_error_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le_s2
import Theorems.Thm_OAI_Erdos3_VectorPolynomial_exists_allocatedSupportedSliced_natural_grid_site_expansion_s2

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.CeilGridScaleRatio
namespace OAI

section

namespace Erdos3

theorem ceilGridScale_ratio_bounds (K : ℕ) (hK : 0 < K) {γ : ℝ} (hγ : 0 < γ) :
    0 < ⌈γ * (K : ℝ)⌉₊ ∧
    γ ≤ (⌈γ * (K : ℝ)⌉₊ : ℝ) / K ∧
    (⌈γ * (K : ℝ)⌉₊ : ℝ) / K ≤ γ + 1 ∧
    (K : ℝ) / ⌈γ * (K : ℝ)⌉₊ ≤ γ⁻¹ := by
  have hKr : (0 : ℝ) < K := Nat.cast_pos.mpr hK
  have hK1 : (1 : ℝ) ≤ K := Nat.one_le_cast.mpr hK
  have hN : 0 < ⌈γ * (K : ℝ)⌉₊ := Nat.ceil_pos.mpr (mul_pos hγ hKr)
  have hNr : (0 : ℝ) < ⌈γ * (K : ℝ)⌉₊ := Nat.cast_pos.mpr hN
  have hlow := Nat.le_ceil (γ * (K : ℝ))
  have hu := Nat.ceil_lt_add_one (mul_nonneg hγ.le hKr.le)
  refine ⟨hN, (le_div_iff₀ hKr).mpr hlow, (div_le_iff₀ hKr).mpr ?_, ?_⟩
  · nlinarith only [hu, hK1]
  · apply (div_le_iff₀ hNr).mpr
    calc
      (K : ℝ) = γ⁻¹ * (γ * (K : ℝ)) := by rw [← mul_assoc, inv_mul_cancel₀ hγ.ne', one_mul]
      _ ≤ γ⁻¹ * ⌈γ * (K : ℝ)⌉₊ := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hγ.le)

theorem ceilGridScale_mass_bound (K d : ℕ) (hK : 0 < K) {γ μ C : ℝ}
    (hγ : 0 < γ) (hμ : 0 ≤ μ) (_hC : 0 ≤ C)
    (hcap : (K : ℝ) ^ d * μ ≤ C) :
    (⌈γ * (K : ℝ)⌉₊ : ℝ) ^ d * μ ≤ (γ + 1) ^ d * C := by
  obtain ⟨_, _, hratio, _⟩ := ceilGridScale_ratio_bounds K hK hγ
  have hK0 : (K : ℝ) ≠ 0 := (Nat.cast_pos.mpr hK).ne'
  have hr : ((⌈γ * (K : ℝ)⌉₊ : ℝ) / K) * K = ⌈γ * (K : ℝ)⌉₊ := div_mul_cancel₀ _ hK0
  calc
    _ = ((⌈γ * (K : ℝ)⌉₊ : ℝ) / K) ^ d * ((K : ℝ) ^ d * μ) := by
      rw [← mul_assoc, ← mul_pow, hr]
    _ ≤ (γ + 1) ^ d * C := mul_le_mul
      (pow_le_pow_left₀ (by positivity) hratio d) hcap (by positivity) (by positivity)

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.SiteTwistCommonModulus
namespace OAI

section

namespace Erdos3.ScalarSiteExpansion

open scoped NNReal

universe u v

variable {S : Type u} {e : ScalarSiteExpansion.{u,v} S}

theorem Bounds.mono {T D C H T' D' C' H' : ℝ} {L L' : ℝ≥0}
    (h : e.Bounds T D C L H) (hT : T ≤ T') (hD : D ≤ D') (hC : C ≤ C')
    (hL : L ≤ L') (hH : H ≤ H') : e.Bounds T' D' C' L' H' :=
  ⟨h.card_le.trans hT, h.period_pos, fun i => (h.period_le i).trans hD,
    h.coefficient_le.trans hC, h.factor_bound, fun i s r => (h.lipschitz i s r).weaken hL,
    fun i s r x hx => h.support i s r x (hH.trans hx)⟩

end Erdos3.ScalarSiteExpansion

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.AllocatedActiveGridPlateau
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
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}

local notation "ig" => allocatedGridIntegerAxis B U b S

omit [∀ j, DecidableEq (I j)] [∀ a, DecidableEq (B a)] in
theorem allocatedGridIntegerAxis_grid (a : gridAxes) :
    allocatedGridAxis (I := I) U b S.value ⟨(ig a).1, Sum.inr (ig a).2⟩ := by
  rcases a with ⟨⟨j, i | i⟩, ha⟩
  · exact False.elim ha
  · exact ha

end Erdos3.VectorPolynomial

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
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Geometry.AllocatedSupportedSlicedNaturalCap
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
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (q : ℕ) (hq : 0 < q) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ t, 0 < H t)
variable (hsubset : ∀ t, integerProgressionSupport (c t) (step t : ℤ) (H t) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U basis S t : ℤ))
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))
variable (j : Fin m) (i : Fin (n j))

local notation "height" => basisAxisScale (basis j) i
local notation "degree" => Fin.val j + 1
local notation "gamma" => principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))

include hq in
theorem allocatedSupportedSlicedPhysicalGridPMF_natural_norm_le
    (hgrid : allocatedGridAxis (I := I) U basis S.value ⟨j,Sum.inr i⟩)
    {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ b v, δ * allocatedPrincipalSides B U basis S ⟨⟨j,Sum.inr i⟩,b,v⟩ ≤
      (H ⟨⟨j,Sum.inr i⟩,b,v⟩ : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ b v, 0 < step ⟨⟨j,Sum.inr i⟩,b,v⟩)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ b v, ((step ⟨⟨j,Sum.inr i⟩,b,v⟩ * q : ℕ) : ℝ) ≤ P)
    (rows : Finset (Finset α)) (hrows : ∀ t ∈ rows, t.card ≤ degree)
    (hBa : positiveModerateSpectrumBlockCount j.val rows.card
      ((layerTailDegree m + 1) * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : uniformSpectrumBlockCount j.val rows.card (degree * rows.card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (x : G → IntegerScalarCubeBox α S.value) (z : rows → ℤ) :
    ‖(((allocatedPrincipalGridScale (G := G) B U basis (R := R) j i : ℝ) ^ rows.card *
      (allocatedSupportedSlicedPhysicalGridPMF B U basis hR hσ S q r H step c hH hsubset hcell j i rows x z).toReal : ℝ) : ℂ)‖ ≤
      (gamma + 1) ^ rows.card * allocatedSlicedGridPointCap (G := G) (α := α) B (R := R) j i δ P T rows.card := by
  have h := allocatedSupportedSlicedPhysicalGridPMF_uniform_norm_le_s2
    B U basis hR hσ S q hq r H step c hH hsubset hcell j i hgrid hδ hdense T hQT hstep
    A hA P hP hcP hsP hstride rows hrows hBa hBi x z
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h ⊢
  exact ceilGridScale_mass_bound height rows.card (basisAxisScale_pos (basis j) i)
    (principalProfileSize_pos (hR j) _) ENNReal.toReal_nonneg
    (le_trans zero_le_one (le_max_left _ _)) h

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

section

namespace Erdos3.VectorPolynomial
open scoped Classical

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
variable (R : Fin m → ℝ) (j : Fin m) (i : Fin (n j))
variable (α : Type*) [Fintype α] (d T : ℕ)
local notation "degree" => Fin.val j + 1

theorem allocatedSlicedGridPointCap_geometry_exp_bound {δ D v w t P p₀ : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀)
    (hδ : 0 < δ) (hR : 0 < R j)
    (hq : (Fintype.card α : ℝ) ≤ D) (hdegree : ((degree : ℕ) : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v)
    (hP : 1 ≤ P) (hPp₀ : P ≤ Real.exp p₀) :
    allocatedSlicedGridPointCap (G := G) (α := α) B (R := R) j i δ P T d ≤
      Real.exp (slicedGridSiteLog j.val d ((layerTailDegree m + 1) * d) (degree * d)
        D (slicedGridGeometryLog D v w t + p₀) 0) := by
  let p := slicedGridGeometryLog D v w t + p₀
  have hg : 0 ≤ slicedGridGeometryLog D v w t := by unfold slicedGridGeometryLog; positivity
  have hp : 0 ≤ p := add_nonneg hg hp₀
  have hgp : Real.exp (slicedGridGeometryLog D v w t) ≤ Real.exp p :=
    Real.exp_le_exp.mpr (le_add_of_nonneg_right hp₀)
  have hPp : P ≤ Real.exp p := hPp₀.trans (Real.exp_le_exp.mpr (le_add_of_nonneg_left hg))
  obtain ⟨hVa, hVi, hWa, hWi, hK, _⟩ := allocatedSlicedGrid_geometry_bounds
    B R j i (Fintype.card α) d T hD hv hw ht hδ hR hq hdegree hd htail hb hRv hRi hδw hT hcoeff
  have hγ := principalProfileSize_pos hR (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
  exact slicedGridPointCap_exp_bound (Fintype.card α) j.val d ((layerTailDegree m + 1) * d) (degree * d)
    (allocatedSlicedGridHeightCutoff (G := G) B (R := R) j i T) hD hp hq hd hP
    (by positivity) (by positivity) (by positivity) (by positivity) hPp
    (hVa.trans hgp) (hVi.trans hgp) (hWa.trans hgp) (hWi.trans hgp) (hK.trans hgp)

theorem allocatedSlicedGridNaturalPointCap_geometry_exp_bound {δ D v w t P p₀ : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀)
    (hδ : 0 < δ) (hR : 0 < R j)
    (hq : (Fintype.card α : ℝ) ≤ D) (hdegree : ((degree : ℕ) : ℝ) ≤ D) (hd : (d : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hb : (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : R j ≤ Real.exp v) (hRi : (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : (Fintype.card (BoundedCoefficientExponent (LayerSamplerVariables G I n B) degree) : ℝ) ≤ Real.exp v)
    (hP : 1 ≤ P) (hPp₀ : P ≤ Real.exp p₀) :
    (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) + 1) ^ d *
    allocatedSlicedGridPointCap (G := G) (α := α) B (R := R) j i δ P T d ≤
      Real.exp (slicedGridSiteLog j.val d ((layerTailDegree m + 1) * d) (degree * d)
        D (slicedGridGeometryLog D v w t + p₀) 0 + D * (v + 1)) := by
  have hcap := allocatedSlicedGridPointCap_geometry_exp_bound B R j i α d T
    hD hv hw ht hp₀ hδ hR hq hdegree hd htail hb hRv hRi hδw hT hcoeff hP hPp₀
  have hγ := principalProfileSize_pos hR (Finset.card (layerIntegerPrincipalSlots (G := G) B j i))
  have hslots : ((layerIntegerPrincipalSlots (G := G) B j i).card : ℝ) ≤ D := by
    simpa only [layerIntegerPrincipalSlots_card] using hb
  have hγv := (principalProfileSize_exp_bounds _ hR hslots hRv hRi).1
  have hadd : principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)) + 1 ≤ Real.exp (v + 1) := by
    simpa only [add_comm 1 (principalProfileSize (R j) (Finset.card (layerIntegerPrincipalSlots (G := G) B j i)))] using one_add_le_exp_succ hv hγv
  have hpow := pow_le_exp_mul_of_le_exp (by positivity) hadd (by positivity) d hd
  have hmul := mul_le_mul hpow hcap
    (le_trans zero_le_one (le_max_left _ _)) (Real.exp_nonneg _)
  exact hmul.trans_eq (by rw [← Real.exp_add]; congr 1; ring)

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open scoped BigOperators Classical NNReal

universe uα

variable {m : ℕ} {G : Type*} [Fintype G]
variable {I : Fin m → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)] {n : Fin m → ℕ}
variable (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)] [∀ a, DecidableEq (B a)]
variable {J : Fin m → Type*} [∀ j, Fintype (J j)]
variable (U : ∀ j, Submodule ℝ (J j → ℝ))
variable (b : ∀ j, Module.Basis (Fin (n j)) ℝ (euclideanSubspace (U j))ᗮ)
variable {R σ : Fin m → ℝ} (hR : ∀ j, 0 < R j) (hσ : ∀ j, 0 < σ j)
variable (S : LayerSamplerScale (G := G) B U b R σ)
variable {α : Type uα} [Fintype α] [DecidableEq α]
variable (rowSets : Fin m → Finset (Finset α))

local notation "gridAxes" => {a // allocatedGridAxis (I := I) U b S.value a}
local notation "ig" => allocatedGridIntegerAxis B U b S
local notation "axisN" => allocatedGridNaturalScale B U b S
local notation "rowTypes" => (fun j : Fin m => {t : Finset α // t ∈ rowSets j})

variable (H step : PrincipalTupleIndex B (layerSamplerDegree I n) → ℕ)
variable (c : PrincipalTupleIndex B (layerSamplerDegree I n) → ℤ) (hH : ∀ j, 0 < H j)
variable (hsubset : ∀ j, integerProgressionSupport (c j) (step j : ℤ) (H j) ⊆
  Finset.Ico (0 : ℤ) (allocatedPrincipalSides B U b S j : ℤ))
variable (q : ℕ) (r : PrincipalTupleIndex B (layerSamplerDegree I n) → Option α → ZMod q)
variable (hcell : 0 < (principalTupleWeights (α := α) B (layerSamplerDegree I n) H hH).mass
  (Finset.univ.filter (fun y => principalResidueLabel q y = r)))

theorem exists_allocatedSupportedSliced_full_grid_site_expansion_s2_oai
    (hq : 0 < q) {δ : ℝ} (hδ : 0 < δ)
    (hdense : ∀ t, δ * allocatedPrincipalSides B U b S t ≤ (H t : ℝ))
    (T : ℕ) (hQT : (((Fintype.card α + 1) * q : ℕ) : ℝ) / δ ≤ T)
    (hstep : ∀ t, 0 < step t)
    (A : ℝ≥0) (hA : LipschitzWith A Real.smoothTransition) (P : ℝ) (hP : 1 ≤ P)
    (hcP : scalarCubePrimitiveEnvelope Empty A 16 (128 * probabilityProfileLipschitz) 1 ≤ P)
    (hsP : scalarCubePrimitiveEnvelope α A 1 0 q ≤ P)
    (hstride : ∀ t, ((step t * q : ℕ) : ℝ) ≤ P)
    (hrows : ∀ j t, t ∈ rowSets j → t.card ≤ j.val + 1)
    (hBa : ∀ j i, positiveModerateSpectrumBlockCount j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    (hBi : ∀ j i, uniformSpectrumBlockCount j.val (rowSets j).card
      ((j.val + 1) * (rowSets j).card) ≤ Fintype.card (B ⟨j,Sum.inr i⟩))
    {D v w t p₀ E ε : ℝ}
    (hD : 0 ≤ D) (hv : 0 ≤ v) (hw : 0 ≤ w) (ht : 0 ≤ t) (hp₀ : 0 ≤ p₀) (hE : 0 ≤ E)
    (hcube : (Fintype.card α : ℝ) ≤ D) (hdegree : ∀ j : Fin m, ((j.val + 1 : ℕ) : ℝ) ≤ D)
    (hrowsD : ∀ j, ((rowSets j).card : ℝ) ≤ D)
    (htail : ((layerTailDegree m + 1 : ℕ) : ℝ) ≤ D)
    (hblocks : ∀ j i, (Fintype.card (B ⟨j, Sum.inr i⟩) : ℝ) ≤ D)
    (hRv : ∀ j, R j ≤ Real.exp v) (hRi : ∀ j, (R j)⁻¹ ≤ Real.exp v)
    (hδw : δ⁻¹ ≤ Real.exp w) (hT : (T : ℝ) ≤ Real.exp t)
    (hcoeff : ∀ j : Fin m, (Fintype.card (BoundedCoefficientExponent
      (LayerSamplerVariables G I n B) (j.val + 1)) : ℝ) ≤ Real.exp v)
    (hPp₀ : P ≤ Real.exp p₀) (haxes : (Fintype.card gridAxes : ℝ) ≤ D)
    (hε : 0 < ε) (hεE : ε⁻¹ ≤ Real.exp E) (hσ1 : ∀ j, σ j ≤ 1) :
    let p := slicedGridGeometryLog D v w t + p₀
    let L := fun j : Fin m => fun e : ℝ => slicedGridSiteLog j.val (rowSets j).card
      ((layerTailDegree m + 1) * (rowSets j).card) ((j.val + 1) * (rowSets j).card) D p e
    let Cp := ∑ j, (L j 0 + D * (v + 1))
    let E' := uniformProductAccuracyLog D Cp E + D * (v + 1) + 1
    let Op := ∑ j, (siteExponentialOutputLog (Fintype.card (Finset α)) (L j E') + (D + 1) * (v + 1))
    ∃ e : gridAxes → ScalarSiteExpansion.{uα,uα} (Finset α),
      (∀ a, (e a).Bounds (Real.exp Op) (Real.exp Op) (Real.exp Op)
        ⟨Real.exp Op, Real.exp_nonneg _⟩ (Real.exp (slicedGridGeometryLog D v w t + (D + v + 8)))) ∧
      ∀ (x : G → IntegerScalarCubeBox α S.value) (z : AllocatedFrozenJetRows B U b S rowTypes),
        ‖(allocatedFullGridNaturalVolume B U b S rowSets : ℂ) *
          (allocatedSupportedSlicedFullGridDensity B U b hR hσ S rowSets H step c hH hsubset q r hcell x z : ℂ) -
          allocatedFullGridSiteApproximation B U b S rowSets e z‖ ≤ ε := by
  intro p L Cp E' Op
  have hp : 0 ≤ p := by dsimp [p, slicedGridGeometryLog]; positivity
  have hL (j : Fin m) {e : ℝ} (he : 0 ≤ e) : 0 ≤ L j e :=
    (slicedGridSiteLog_bounds j.val (rowSets j).card _ _ hD hp he).1
  have hCp : 0 ≤ Cp := Finset.sum_nonneg (fun j _ => add_nonneg (hL j le_rfl) (by positivity))
  let C := Real.exp Cp
  let η := uniformProductAccuracy (Fintype.card gridAxes) C ε
  obtain ⟨hη, hη1, _⟩ := uniformProductAccuracy_spec (Fintype.card gridAxes) (Real.exp_nonneg Cp) hε
  have hηE := uniformProductAccuracy_inverse_exp_bound (Fintype.card gridAxes)
    (Real.exp_nonneg Cp) hε hD hCp hE haxes le_rfl hεE
  have hEt : 0 ≤ uniformProductAccuracyLog D Cp E := uniformProductAccuracyLog_nonneg hD hCp hE
  have hE' : 0 ≤ E' := by dsimp [E']; positivity
  have hbound (j : Fin m) : L j 0 + D * (v + 1) ≤ Cp :=
    Finset.single_le_sum (fun k _ => add_nonneg (hL k le_rfl) (by positivity)) (Finset.mem_univ j)
  have hcap (a : gridAxes) (x : G → IntegerScalarCubeBox α S.value) (z : rowSets (ig a).1 → ℤ) :
      ‖(((axisN a : ℝ) ^ (rowSets (ig a).1).card *
        (allocatedSupportedSlicedPhysicalGridPMF B U b hR hσ S q r H step c hH hsubset hcell
          (ig a).1 (ig a).2 (rowSets (ig a).1) x z).toReal : ℝ) : ℂ)‖ ≤ C := by
    have hc := allocatedSupportedSlicedPhysicalGridPMF_natural_norm_le B U b hR hσ S q hq r H step c hH hsubset hcell
      (ig a).1 (ig a).2 (allocatedGridIntegerAxis_grid B U b S a) hδ
      (fun b v => hdense _) T hQT (fun b v => hstep _) A hA P hP hcP hsP (fun b v => hstride _)
      (rowSets (ig a).1) (hrows (ig a).1) (hBa _ _) (hBi _ _) x z
    have hb := allocatedSlicedGridNaturalPointCap_geometry_exp_bound B R (ig a).1 (ig a).2 α
      (rowSets (ig a).1).card T hD hv hw ht hp₀ hδ (hR _) hcube (hdegree _) (hrowsD _)
      htail (hblocks _ _) (hRv _) (hRi _) hδw hT (hcoeff _) hP hPp₀
    exact hc.trans (hb.trans (Real.exp_le_exp.mpr (hbound _)))
  have hex (a : gridAxes) := exists_allocatedSupportedSliced_natural_grid_site_expansion_s2
    B U b hR hσ S q hq r H step c hH hsubset hcell (ig a).1 (ig a).2
    (allocatedGridIntegerAxis_grid B U b S a) hδ (fun b v => hdense _) T hQT (fun b v => hstep _)
    A hA P hP hcP hsP (fun b v => hstride _) (rowSets (ig a).1) (hrows (ig a).1) (hBa _ _) (hBi _ _)
    hD hv hw ht hp₀ hEt hcube (hdegree _) (hrowsD _) htail (hblocks _ _) (hRv _) (hRi _)
    hδw hT (hcoeff _) hPp₀ hη hη1 hηE (hσ1 _)
  choose e he herr using hex
  refine ⟨e, ?_, ?_⟩
  · intro a
    have hO : siteExponentialOutputLog (Fintype.card (Finset α)) (L (ig a).1 E') + (D + 1) * (v + 1) ≤ Op :=
      Finset.single_le_sum (fun k _ => add_nonneg
        (siteExponentialOutputLog_nonneg _ (hL k hE')) (by positivity)) (Finset.mem_univ (ig a).1)
    have hb := Real.exp_le_exp.mpr hO
    exact (he a).mono hb hb hb (NNReal.coe_le_coe.mp hb) le_rfl
  · exact allocatedSupportedSlicedFullGridNaturalSite_error_s2 B U b hR hσ S rowSets H step c hH hsubset q r hcell
      e (Real.exp_nonneg Cp) hε hcap herr

end Erdos3.VectorPolynomial

end

end OAI
end

theorem solution.{uα, u_1, u_2, u_3, u_4} : type_of% @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_full_grid_site_expansion_s2_oai.{uα, u_1, u_2, u_3, u_4} := @OAI.Erdos3.VectorPolynomial.exists_allocatedSupportedSliced_full_grid_site_expansion_s2_oai.{uα, u_1, u_2, u_3, u_4}
