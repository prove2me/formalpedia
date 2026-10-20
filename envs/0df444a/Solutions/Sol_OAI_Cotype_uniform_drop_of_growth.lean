-- Prove2me | solution 1 for OAI.Cotype.uniform_drop_of_growth
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:40:47.84964+00:00
-- url     : https://prove2.me/submissions/fe9a7a11-4c42-4aaa-9ef4-cc34ff1807fe

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

open OAI OAI.Cotype
lemma h51_fastchain (m P j : ℕ) (w : ℕ → ℝ)
    (hfast : ∀ i, i < j → 2 * w (P - 2*m*i) < w (P - 2*m*i - 2*m)) :
    2 ^ j * w P ≤ w (P - 2*m*j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 := ih (fun i hi => hfast i (by omega))
    have h2 := hfast j (by omega)
    have e : P - 2*m*j - 2*m = P - 2*m*(j+1) := by
      rw [Nat.sub_sub, mul_add, mul_one]
    rw [e] at h2
    rw [pow_succ]; nlinarith

lemma h51_step (m L n₀ : ℕ) (c : ℝ) (w : ℕ → ℝ) (hw : ∀ n, 0 < w n) (hanti : Antitone w)
    (hL : 1 < 2 ^ L * c) (hn₀ : 2*m*(L+2) < n₀)
    (hslow : ∀ n, 4*m < n → w (n-2*m) ≤ 2*w n → c*w n ≤ w (2*(n-2*m)))
    (k : ℕ) (hk : n₀ ≤ k) (hks : w (k-2*m) ≤ 2*w k) :
    ∃ k', 2*k ≤ k' + 2*m*(L+2) ∧ c * w k ≤ w k' ∧ w (k'-2*m) ≤ 2*w k' := by
  have hk4 : 4*m < k := by nlinarith
  have hc := hslow k hk4 hks
  set P := 2*(k-2*m) with hP
  by_contra hcon
  push_neg at hcon
  have hfast : ∀ i, i < L → 2 * w (P - 2*m*i) < w (P - 2*m*i - 2*m) := by
    intro i hi
    have hle : P - 2*m*i ≤ P := Nat.sub_le _ _
    have h1 := hcon (P - 2*m*i) (by
      have : 2*m*i ≤ 2*m*L := Nat.mul_le_mul_left _ hi.le
      have : 2*m*(L+2) = 2*m*L + 4*m := by ring
      omega) (le_trans (hc) (hanti hle))
    linarith
  have hch := h51_fastchain m P L w hfast
  have hge : k ≤ P - 2*m*L := by
    have : 2*m*(L+2) = 2*m*L + 4*m := by ring
    omega
  have h3 := hanti hge
  have hwk := hw k
  have : 2 ^ L * (c * w k) ≤ 2 ^ L * w P := mul_le_mul_of_nonneg_left hc (by positivity)
  nlinarith

theorem solution (m : ℕ) (hm : 0 < m) (c q : ℝ)
    (hc : 0 < c) (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ n₀ : ℕ, 4*m < n₀ ∧ ∀ w : ℕ → ℝ,
      (∀ n, 0 < w n) → Antitone w →
      (∃ D : ℝ, ∀ n, w n ≤ D*q^n) →
      (∀ n, 4*m < n → w (n-2*m) ≤ 2*w n → c*w n ≤ w (2*(n-2*m))) →
      ∀ n, n₀ ≤ n → 2*w n < w (n-2*m) := by
  obtain ⟨L, hL⟩ := pow_unbounded_of_one_lt (1 / c) (by norm_num : (1:ℝ) < 2)
  have hL' : 1 < 2 ^ L * c := by
    rw [div_lt_iff₀ hc] at hL; linarith
  obtain ⟨N1, hN1⟩ := exists_pow_lt_of_lt_one hc hq1
  set A := 2*m*(L+2) with hA
  refine ⟨A + 1 + N1, by
    have : 2*m*(L+2) = 2*m*L + 4*m := by ring
    omega, ?_⟩
  intro w hw hanti ⟨D, hD⟩ hslow n hn
  by_contra hns
  push_neg at hns
  -- chain
  have chain : ∀ i : ℕ, ∃ k, n + i * (1 + N1) ≤ k ∧ c ^ i * w n ≤ w k ∧ w (k-2*m) ≤ 2*w k := by
    intro i
    induction i with
    | zero => exact ⟨n, by simp, by simp, hns⟩
    | succ i ih =>
      obtain ⟨k, hk1, hk2, hk3⟩ := ih
      obtain ⟨k', h1, h2, h3⟩ := h51_step m L (A + 1 + N1) c w hw hanti hL' (by omega) hslow k
        (by nlinarith) hk3
      refine ⟨k', by
        have : n + (i+1) * (1 + N1) = n + i * (1+N1) + (1 + N1) := by ring
        omega, ?_, h3⟩
      rw [pow_succ]
      calc c ^ i * c * w n = c * (c ^ i * w n) := by ring
        _ ≤ c * w k := mul_le_mul_of_nonneg_left hk2 hc.le
        _ ≤ w k' := h2
  -- contradiction
  have hqs : q ^ (1 + N1) < c := by
    calc q ^ (1 + N1) ≤ q ^ N1 := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
      _ < c := hN1
  set r := c / q ^ (1 + N1) with hr
  have hr1 : 1 < r := by rw [hr, lt_div_iff₀ (by positivity)]; linarith
  obtain ⟨i, hi⟩ := pow_unbounded_of_one_lt (D / w n) hr1
  obtain ⟨k, hk1, hk2, -⟩ := chain i
  have hDk := hD k
  have hqk : q ^ k ≤ q ^ (i * (1 + N1)) := pow_le_pow_of_le_one hq0.le hq1.le (by omega)
  have hwn := hw n
  have hDpos : 0 ≤ D := by
    have := hw 0; have := hD 0; simp at this; linarith
  have e1 : c ^ i = r ^ i * (q ^ (1+N1)) ^ i := by
    rw [hr, div_pow, div_mul_cancel₀]; positivity
  have e2 : (q ^ (1+N1)) ^ i = q ^ (i * (1+N1)) := by rw [← pow_mul, mul_comm]
  rw [div_lt_iff₀ hwn] at hi
  have hpos : 0 < q ^ (i * (1 + N1)) := by positivity
  have : r ^ i * w n * q ^ (i * (1 + N1)) ≤ D * q ^ (i * (1 + N1)) := by
    calc r ^ i * w n * q ^ (i * (1 + N1)) = c ^ i * w n := by rw [e1, e2]; ring
      _ ≤ w k := hk2
      _ ≤ D * q ^ k := hDk
      _ ≤ D * q ^ (i * (1 + N1)) := mul_le_mul_of_nonneg_left hqk hDpos
  have := le_of_mul_le_mul_right this hpos
  linarith

