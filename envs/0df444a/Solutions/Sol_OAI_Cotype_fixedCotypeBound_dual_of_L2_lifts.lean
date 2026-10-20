-- Prove2me | solution 1 for OAI.Cotype.fixedCotypeBound_dual_of_L2_lifts
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:32:04.582673+00:00
-- url     : https://prove2.me/submissions/80f5ef2e-8a8b-4471-8d58-fbc0c923d387

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

open OAI OAI.Cotype
open scoped BigOperators
open WithLp
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem h50a_eval (φ : X →L[ℝ] ℝ) {a : ℝ} (ha : a < ‖φ‖) :
    ∃ x : X, ‖x‖ ≤ 1 ∧ a < φ x := by
  rcases lt_or_ge a 0 with h | h
  · exact ⟨0, by simp, by simpa using h⟩
  obtain ⟨x, hx1, hx2⟩ := φ.exists_lt_apply_of_lt_opNorm (r := a) ha
  rcases le_or_gt 0 (φ x) with h0 | h0
  · exact ⟨x, hx1.le, by rwa [Real.norm_eq_abs, abs_of_nonneg h0] at hx2⟩
  · refine ⟨-x, by rw [norm_neg]; exact hx1.le, ?_⟩
    rw [map_neg]
    rwa [Real.norm_eq_abs, abs_of_neg h0] at hx2

theorem h50a_l2norm {Ω : Type*} [Fintype Ω] (g : Ω → (X →L[ℝ] ℝ)) :
    ‖finiteL2Dual g‖ = ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ := by
  set N := ‖(toLp 2 g : PiLp 2 (fun _ : Ω => (X →L[ℝ] ℝ)))‖ with hN
  have hN2 : N ^ 2 = ∑ a, ‖g a‖ ^ 2 := by
    rw [hN, PiLp.norm_sq_eq_of_L2]
  apply le_antisymm
  · exact ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (finiteL2DualLinear_bound g)
  · set F := finiteL2Dual g
    have key : ∀ δ > 0, N ^ 2 ≤ ‖F‖ * N + δ := by
      intro δ hδ
      set S := ∑ a, ‖g a‖
      have hS : 0 ≤ S := Finset.sum_nonneg fun a _ => norm_nonneg _
      have he : 0 < δ / (S + 1) := by positivity
      choose x hx1 hx2 using fun a => h50a_eval (g a) (sub_lt_self (‖g a‖) he)
      let z : PiLp 2 (fun _ : Ω => X) := toLp 2 (fun a => ‖g a‖ • x a)
      have hz : ‖z‖ ≤ N := by
        rw [hN, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum; intro a _
        simp only [z, PiLp.toLp_apply, norm_smul, norm_norm]
        exact pow_le_pow_left₀ (by positivity)
          (by simpa using mul_le_mul_of_nonneg_left (hx1 a) (norm_nonneg (g a))) 2
      have hFz : F z ≤ ‖F‖ * N :=
        (Real.le_norm_self _).trans ((F.le_opNorm z).trans
          (mul_le_mul_of_nonneg_left hz (norm_nonneg _)))
      have hlow : ∑ a, ‖g a‖ * (‖g a‖ - δ / (S + 1)) ≤ F z := by
        simp only [F, finiteL2Dual_apply, z, PiLp.toLp_apply, map_smul, smul_eq_mul]
        exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hx2 a).le (norm_nonneg _)
      have hlow' : ∑ a, ‖g a‖ * (‖g a‖ - δ / (S + 1)) = N ^ 2 - S * (δ / (S + 1)) := by
        rw [hN2]; simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, sq, S]
      have : S * (δ / (S + 1)) ≤ δ := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
      linarith
    have h2 : N ^ 2 ≤ ‖F‖ * N := le_of_forall_pos_le_add fun δ hδ => key δ hδ
    rcases (norm_nonneg _ : (0:ℝ) ≤ N).eq_or_lt with h0 | h0
    · rw [hN, ← h0]; exact norm_nonneg _
    · nlinarith

theorem t_avg {X Y : Type*} [NormedAddCommGroup X] [NormedAddCommGroup Y] {n : ℕ} (f : Cube n → X) (g : Cube n → Y) :
    average (fun u => ‖f u‖ * ‖g u‖) ≤ cubeL2 X f * cubeL2 Y g := by
  simp only [average, cubeL2, smul_eq_mul]
  have hN : (0 : ℝ) ≤ (Fintype.card (Cube n) : ℝ)⁻¹ := by positivity
  rw [Real.sqrt_mul hN, Real.sqrt_mul hN]
  have h := Real.sum_mul_le_sqrt_mul_sqrt Finset.univ (fun u => ‖f u‖) (fun u => ‖g u‖)
  calc (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, ‖f u‖ * ‖g u‖
      ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * (√(∑ u, ‖f u‖ ^ 2) * √(∑ u, ‖g u‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left h hN
    _ = _ := by
      rw [show √(Fintype.card (Cube n) : ℝ)⁻¹ * √(∑ u, ‖f u‖ ^ 2) * (√(Fintype.card (Cube n) : ℝ)⁻¹ *
        √(∑ u, ‖g u‖ ^ 2)) = (√(Fintype.card (Cube n) : ℝ)⁻¹ * √(Fintype.card (Cube n) : ℝ)⁻¹) *
        (√(∑ u, ‖f u‖ ^ 2) * √(∑ u, ‖g u‖ ^ 2)) by ring, Real.mul_self_sqrt hN]

theorem solution {m : ℕ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ z : Fin m → X, ∃ H : Cube m → X,
      (∀ i, moment X H i = z i) ∧ cubeL2 X H ≤ C * Real.sqrt (∑ i, ‖z i‖^2)) :
    FixedCotypeBound (X →L[ℝ] ℝ) m C := by
  refine ⟨hC, fun φ => ?_⟩
  have hn : Real.sqrt (∑ i, ‖φ i‖ ^ 2) = ‖finiteL2Dual φ‖ := by
    rw [h50a_l2norm, PiLp.norm_eq_of_L2]
  rw [hn]
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC (cubeL2_nonneg _)) fun z => ?_
  obtain ⟨H, hH1, hH2⟩ := h (fun i => z i)
  have hz : Real.sqrt (∑ i, ‖z i‖ ^ 2) = ‖z‖ := by rw [PiLp.norm_eq_of_L2]
  rw [hz] at hH2
  have e : finiteL2Dual φ z =
      average (fun ε => (rademacherSum (X →L[ℝ] ℝ) φ ε) (H ε)) := by
    rw [finiteL2Dual_apply]
    simp only [← hH1, moment, average, smul_eq_mul, map_smul, map_sum, rademacherSum,
      ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
      Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [e]
  calc ‖average (fun ε => (rademacherSum (X →L[ℝ] ℝ) φ ε) (H ε))‖
      ≤ average (fun ε => ‖rademacherSum (X →L[ℝ] ℝ) φ ε‖ * ‖H ε‖) := by
        refine (norm_average_le _).trans ?_
        simp only [average, smul_eq_mul]
        exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ε _ => (ContinuousLinearMap.le_opNorm _ _))
          (by positivity)
    _ ≤ cubeL2 _ (rademacherSum (X →L[ℝ] ℝ) φ) * cubeL2 X H := t_avg _ _
    _ ≤ cubeL2 _ (rademacherSum (X →L[ℝ] ℝ) φ) * (C * ‖z‖) :=
        mul_le_mul_of_nonneg_left hH2 (cubeL2_nonneg _)
    _ = C * cubeL2 _ (rademacherSum (X →L[ℝ] ℝ) φ) * ‖z‖ := by ring

