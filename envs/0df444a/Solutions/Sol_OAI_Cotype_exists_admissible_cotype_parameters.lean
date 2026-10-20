-- Prove2me | solution 1 for OAI.Cotype.exists_admissible_cotype_parameters
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:38:44.314002+00:00
-- url     : https://prove2.me/submissions/6e66f374-a67a-47fe-bcca-cfc329632ee7

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality
import Definitions.Def_OAI_Analysis_Cotype_Rectangles
import Definitions.Def_OAI_Analysis_Cotype_BinaryRank
import Definitions.Def_OAI_Analysis_Cotype_BiasedFourier
import Definitions.Def_OAI_Analysis_Cotype_Damping
import Definitions.Def_OAI_Analysis_Cotype_WalshExactPairing
import Definitions.Def_OAI_Analysis_Cotype_WalshSymmetry
import Definitions.Def_OAI_Analysis_Cotype_CubeCoordinateProjections
import Definitions.Def_OAI_Analysis_Cotype_CubeFirstChaos
import Definitions.Def_OAI_Analysis_Cotype_FrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_BinaryCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshFrameOrbit
import Definitions.Def_OAI_Analysis_Cotype_FrameFeasibility
import Definitions.Def_OAI_Analysis_Cotype_EquivariantLifts
import Definitions.Def_OAI_Analysis_Cotype_DualAction
import Definitions.Def_OAI_Analysis_Cotype_EquivariantPairing
import Definitions.Def_OAI_Analysis_Cotype_FrameLifts
import Definitions.Def_OAI_Analysis_Cotype_L2MomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteLevelTower
import Definitions.Def_OAI_Analysis_Cotype_WeightedCompact
import Definitions.Def_OAI_Analysis_Cotype_CompactQuotient
import Definitions.Def_OAI_Analysis_Cotype_GrowthTuplePairing
import Definitions.Def_OAI_Analysis_Cotype_PatternPairing
import Definitions.Def_OAI_Analysis_Cotype_TaggedFrames
import Definitions.Def_OAI_Analysis_Cotype_CoefficientTarget
import Definitions.Def_OAI_Analysis_Cotype_DampedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_GroupedPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ProjectionCoefficients
import Definitions.Def_OAI_Analysis_Cotype_PatternNormalization
import Definitions.Def_OAI_Analysis_Cotype_PatternProjections
import Definitions.Def_OAI_Analysis_Cotype_DeletedTail
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevBounds
import Definitions.Def_OAI_Analysis_Cotype_ChebyshevTruncation
import Definitions.Def_OAI_Analysis_Cotype_BivariateSplit
import Definitions.Def_OAI_Analysis_Cotype_ProjectionDerivatives
import Definitions.Def_OAI_Analysis_Cotype_MixedDerivative
import Definitions.Def_OAI_Analysis_Cotype_CoefficientCompactness
import Definitions.Def_OAI_Analysis_Cotype_GrowthScalarData
import Definitions.Def_OAI_Analysis_Cotype_TaggedCoefficient
import Definitions.Def_OAI_Analysis_Cotype_RankWalsh
import Definitions.Def_OAI_Analysis_Cotype_UniformDecay
import Definitions.Def_OAI_Analysis_Cotype_CompactDomain

open OAI OAI.Cotype
lemma h51_log4 (x : ℝ) (hx : 4 ≤ x) : 2 ≤ Real.logb 2 x := by
  have h4 : Real.logb 2 4 = 2 := by
    rw [show (4:ℝ) = 2 ^ (2:ℕ) by norm_num, Real.logb_pow]
    simp [Real.logb_self_eq_one]
  calc (2:ℝ) = Real.logb 2 4 := h4.symm
    _ ≤ _ := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hx

lemma h51_key (s C : ℝ) (hs : 0 < s) (hC : 0 < C) :
    ∀ᶠ m : ℕ in Filter.atTop, C * (Real.logb 2 (m : ℝ)) ^ 3 ≤ (m : ℝ) ^ s := by
  have hlo := ((isLittleO_log_rpow_rpow_atTop (3 : ℝ) hs).comp_tendsto
    tendsto_natCast_atTop_atTop)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc : 0 < (Real.log 2) ^ 3 / C := by positivity
  filter_upwards [hlo.bound hc, Filter.eventually_ge_atTop 1] with m hm hm1
  simp only [Function.comp] at hm
  have hm1' : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hlog : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hm1'
  have hpow : 0 ≤ (m : ℝ) ^ s := Real.rpow_nonneg (by linarith) _
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _), Real.norm_of_nonneg hpow] at hm
  rw [show ((3 : ℝ)) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at hm
  rw [Real.logb, div_pow]
  have : C * (Real.log m ^ 3 / Real.log 2 ^ 3) = (C / Real.log 2 ^ 3) * Real.log m ^ 3 := by ring
  rw [this]
  calc C / Real.log 2 ^ 3 * Real.log m ^ 3 ≤ C / Real.log 2 ^ 3 * (Real.log 2 ^ 3 / C * (m : ℝ) ^ s) :=
        mul_le_mul_of_nonneg_left hm (by positivity)
    _ = (m : ℝ) ^ s := by field_simp

lemma h51_bound (m : ℕ) (K C a e : ℝ) (hK : 0 < K) (hC : 0 < C) (ha : a = 1/2 - e) (he : 0 < e)
    (hm4 : 4 ≤ m) (hkey : 3840 * 48 * K * C * (Real.logb 2 (m : ℝ)) ^ 3 ≤ (m : ℝ) ^ e) :
    80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
      (m : ℝ) * (1 / (2 * 24 * (K * (C * (m : ℝ) ^ a)) * Real.sqrt m)) := by
  have hm : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hm0 : (0 : ℝ) < m := by linarith
  set L := Real.logb 2 (m : ℝ) with hL
  have hL1 : 2 ≤ L := by
    rw [hL]; exact h51_log4 _ hm
  have hd : (degreeCutoff m : ℝ) ≤ 2 * L + 1 := by
    unfold degreeCutoff
    have := Nat.ceil_lt_add_one (show (0:ℝ) ≤ 2 * Real.logb 2 (m : ℝ) by rw [← hL]; linarith)
    rw [← hL] at this; linarith
  have hd0 : (0 : ℝ) ≤ degreeCutoff m := Nat.cast_nonneg _
  have h1 : 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤ 3840 * L ^ 3 := by
    have e1 : (degreeCutoff m : ℝ) ≤ 3 * L := by linarith
    have e2 : (degreeCutoff m : ℝ) + 1 ≤ 4 * L := by linarith
    have e3 : ((degreeCutoff m : ℝ) + 1) ^ 2 ≤ (4 * L) ^ 2 := pow_le_pow_left₀ (by linarith) e2 2
    calc 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤ 80 * (3 * L) * (4 * L) ^ 2 := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left e1 (by norm_num)) e3 (by positivity) (by positivity)
      _ = 3840 * L ^ 3 := by ring
  have hsq : Real.sqrt m = (m : ℝ) ^ (1/2 : ℝ) := Real.sqrt_eq_rpow _
  have hma : (m : ℝ) ^ a * Real.sqrt m = (m : ℝ) ^ (1 - e) := by
    rw [hsq, ← Real.rpow_add hm0, ha]; ring_nf
  have hmm : (m : ℝ) = (m : ℝ) ^ (1 - e) * (m : ℝ) ^ e := by
    rw [← Real.rpow_add hm0]; simp
  have hpos : 0 < (m : ℝ) ^ (1 - e) := Real.rpow_pos_of_pos hm0 _
  have hden : 2 * 24 * (K * (C * (m : ℝ) ^ a)) * Real.sqrt m = 48 * K * C * (m : ℝ) ^ (1 - e) := by
    rw [← hma]; ring
  rw [hden]
  rw [mul_one_div, le_div_iff₀ (by positivity)]
  calc 80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 * (48 * K * C * (m : ℝ) ^ (1 - e))
        ≤ 3840 * L ^ 3 * (48 * K * C * (m : ℝ) ^ (1 - e)) :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
    _ = (3840 * 48 * K * C * L ^ 3) * (m : ℝ) ^ (1 - e) := by ring
    _ ≤ (m : ℝ) ^ e * (m : ℝ) ^ (1 - e) := mul_le_mul_of_nonneg_right hkey hpos.le
    _ = m := by rw [mul_comm, ← hmm]

theorem solution (q r CF CY : ℝ)
    (hq : 2 ≤ q) (hr : 2 ≤ r) (hCF : 1 ≤ CF) (hCY : 1 ≤ CY) :
    ∃ m : ℕ, 0 < m ∧
      1 ≤ CY*(m : ℝ)^(1/2-1/r) ∧ 1 ≤ CF*(m : ℝ)^(1/2-1/q) ∧
      4 ≤ degreeCutoff m ∧ degreeCutoff m < m ∧
      80 * (degreeCutoff m : ℝ) * (degreeCutoff m + 1 : ℝ)^2 ≤
        min ((m : ℝ)*(1/(2*24*(12*(CY*(m : ℝ)^(1/2-1/r)))*Real.sqrt m)))
          ((m : ℝ)*(1/(2*24*(CF*(m : ℝ)^(1/2-1/q))*Real.sqrt m))) := by
  have hr' : 0 < 1 / r := by positivity
  have hq' : 0 < 1 / q := by positivity
  obtain ⟨m, hm⟩ := ((h51_key (1/r) (3840 * 48 * 12 * CY) hr' (by positivity)).and
    ((h51_key (1/q) (3840 * 48 * 1 * CF) hq' (by positivity)).and
      (Filter.eventually_ge_atTop 4))).exists
  obtain ⟨k1, k2, hm4⟩ := hm
  have hm4' : (4:ℝ) ≤ m := by exact_mod_cast hm4
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have ea : 0 ≤ (1/2 - 1/r : ℝ) := by
    have : 1 / r ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hr
    linarith
  have eb : 0 ≤ (1/2 - 1/q : ℝ) := by
    have : 1 / q ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hq
    linarith
  have hA := h51_bound m 12 CY _ (1/r) (by norm_num) (by linarith) rfl hr' hm4 k1
  have hB := h51_bound m 1 CF _ (1/q) (by norm_num) (by linarith) rfl hq' hm4 k2
  simp only [one_mul] at hB
  have hY : 1 ≤ CY * (m : ℝ) ^ (1/2 - 1/r) := one_le_mul_of_one_le_of_one_le hCY (Real.one_le_rpow hm1 ea)
  have hF : 1 ≤ CF * (m : ℝ) ^ (1/2 - 1/q) := one_le_mul_of_one_le_of_one_le hCF (Real.one_le_rpow hm1 eb)
  have hd4 : 4 ≤ degreeCutoff m := by
    unfold degreeCutoff
    apply Nat.add_one_le_iff.mpr
    rw [Nat.lt_ceil]
    have : (2 : ℝ) ≤ Real.logb 2 (m : ℝ) := h51_log4 _ hm4'
    push_cast; linarith
  refine ⟨m, by omega, hY, hF, hd4, ?_, le_min hA hB⟩
  have hsq : 1 ≤ Real.sqrt (m : ℝ) := by rw [Real.one_le_sqrt]; exact hm1
  have hden : 1 ≤ 2 * 24 * (12 * (CY * (m : ℝ) ^ (1/2 - 1/r))) * Real.sqrt m := by
    nlinarith
  have hle : (m : ℝ) * (1 / (2 * 24 * (12 * (CY * (m : ℝ) ^ (1/2 - 1/r))) * Real.sqrt m)) ≤ m := by
    rw [mul_one_div, div_le_iff₀ (by linarith)]; nlinarith
  have hd4' : (4 : ℝ) ≤ degreeCutoff m := by exact_mod_cast hd4
  have : (degreeCutoff m : ℝ) < m := by nlinarith
  exact_mod_cast this

