-- Prove2me | solution 1 for OAI.Cotype.compactMap_walsh_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T22:03:22.580311+00:00
-- url     : https://prove2.me/submissions/e4255a44-2bf2-418d-a84f-06eedb1eb59c

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
open scoped BigOperators
variable {X Y G : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
section h51
variable {X₁ Y₁ : Type*} [NormedAddCommGroup X₁] [NormedSpace ℝ X₁]
  [NormedAddCommGroup Y₁] [NormedSpace ℝ Y₁]
theorem h51w_cubeL2_le_of_le {n : ℕ} (f : Cube n → Y₁) (c : ℝ) (hc : 0 ≤ c) (h : ∀ u, ‖f u‖ ≤ c) :
    cubeL2 Y₁ f ≤ c := by
  unfold cubeL2
  rw [Real.sqrt_le_left hc]
  have hN : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [average, smul_eq_mul]
  calc (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ u, ‖f u‖ ^ 2 ≤ (Fintype.card (Cube n) : ℝ)⁻¹ * ∑ _u : Cube n, c ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum fun u _ => pow_le_pow_left₀ (norm_nonneg _) (h u) 2
    _ = c ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

theorem h51w_cubeL2_map {n : ℕ} (T : X₁ →L[ℝ] Y₁) (f : Cube n → X₁) :
    cubeL2 Y₁ (fun u => T (f u)) ≤ ‖T‖ * cubeL2 X₁ f := by
  unfold cubeL2
  rw [← Real.sqrt_sq (norm_nonneg T), ← Real.sqrt_mul (sq_nonneg _)]
  apply Real.sqrt_le_sqrt
  simp only [average, smul_eq_mul]
  rw [mul_left_comm]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u _
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (T.le_opNorm _) 2

theorem h51w_opW_bound {n : ℕ} (T : X₁ →L[ℝ] Y₁) (f : Cube n → X₁) :
    cubeL2 Y₁ (operatorWalsh T f) ≤ ‖T‖ * cubeL2 X₁ f :=
  h51w_cubeL2_le_of_le _ _ (mul_nonneg (norm_nonneg _) (cubeL2_nonneg _)) fun v =>
    (vectorWalsh_bound (fun u => T (f u)) v).trans (h51w_cubeL2_map T f)

theorem h51w_opW_sub {n : ℕ} (A B : X₁ →L[ℝ] Y₁) (f : Cube n → X₁) :
    operatorWalsh A f - operatorWalsh B f = operatorWalsh (A - B) f := by
  funext v
  simp only [operatorWalsh, vectorWalsh, average, Pi.sub_apply, ← smul_sub, ← Finset.sum_sub_distrib,
    ContinuousLinearMap.sub_apply]

theorem h51w_cubeL2_sub {n : ℕ} (f g : Cube n → Y₁) :
    |cubeL2 Y₁ f - cubeL2 Y₁ g| ≤ cubeL2 Y₁ (f - g) := by
  have e : ∀ h : Cube n → Y₁, cubeL2 Y₁ h = Real.sqrt ((Fintype.card (Cube n) : ℝ)⁻¹) *
      ‖(WithLp.toLp 2 h : PiLp 2 (fun _ : Cube n => Y₁))‖ := fun h => by
    rw [PiLp.norm_eq_of_L2]
    simp only [cubeL2, average, smul_eq_mul]
    exact Real.sqrt_mul (by positivity) _
  rw [e, e, e, ← mul_sub, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
  have := abs_norm_sub_norm_le (WithLp.toLp 2 f : PiLp 2 (fun _ : Cube n => Y₁)) (WithLp.toLp 2 g)
  simpa [← WithLp.toLp_sub] using this

theorem h51t_opWL {n : ℕ} (A B : X₁ →L[ℝ] Y₁) (f : Cube n → X₁) :
    |cubeL2 Y₁ (operatorWalsh A f) - cubeL2 Y₁ (operatorWalsh B f)| ≤ ‖A-B‖ * cubeL2 X₁ f := by
  refine (h51w_cubeL2_sub _ _).trans ?_
  rw [h51w_opW_sub]
  exact h51w_opW_bound _ f

theorem h51w_bdd (n : ℕ) (T : X₁ →L[ℝ] Y₁) : BddAbove (walshOutputs n T) :=
  ⟨‖T‖, by
    rintro r ⟨f, hf, rfl⟩
    exact (h51w_opW_bound T f).trans (by simpa using mul_le_mul_of_nonneg_left hf (norm_nonneg T))⟩

theorem h51w_ne (n : ℕ) (T : X₁ →L[ℝ] Y₁) : (walshOutputs n T).Nonempty :=
  ⟨_, 0, by simp [cubeL2, average], rfl⟩

theorem h51w_le (n : ℕ) (A B : X₁ →L[ℝ] Y₁) : walshNorm n A ≤ walshNorm n B + ‖A - B‖ := by
  apply csSup_le (h51w_ne n A)
  rintro r ⟨f, hf, rfl⟩
  have h1 := h51t_opWL A B f
  have h2 : cubeL2 Y₁ (operatorWalsh B f) ≤ walshNorm n B := le_csSup (h51w_bdd n B) ⟨f, hf, rfl⟩
  have h3 : ‖A - B‖ * cubeL2 X₁ f ≤ ‖A - B‖ := by
    simpa using mul_le_mul_of_nonneg_left hf (norm_nonneg (A - B))
  linarith [(abs_le.mp h1).2]

end h51

theorem solution (hAP : ApproximationProperty X)
    (J : G →L[ℝ] X) (hJ : IsCompactOperator J) (n : ℕ) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hfin : ∀ T : G →L[ℝ] X, FiniteDimensional ℝ (LinearMap.range T.toLinearMap) →
      walshNorm n T ≤ ρ * ‖T‖) :
    walshNorm n J ≤ ρ * ‖J‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  set δ := ε / (ρ + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨S, hSfin, hS⟩ := hAP _ (hJ.isCompact_closure_image_closedBall 1) δ hδ0
  set T := S.comp J with hT
  have hTfin : FiniteDimensional ℝ (LinearMap.range T.toLinearMap) := by
    apply Submodule.finiteDimensional_of_le (S₂ := LinearMap.range S.toLinearMap)
    rintro _ ⟨g, rfl⟩
    exact ⟨J g, rfl⟩
  have hTJ : ‖J - T‖ ≤ δ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm hδ0.le
    intro g hg
    have hmem : J g ∈ closure (J '' Metric.closedBall 0 1) :=
      subset_closure ⟨g, by simp [hg], rfl⟩
    have := hS _ hmem
    rw [ContinuousLinearMap.sub_apply, norm_sub_rev]
    exact this.le
  have h1 := h51w_le n J T
  have h2 := hfin T hTfin
  have h3 : ‖T‖ ≤ ‖J‖ + δ := by
    have := norm_sub_norm_le T J
    rw [norm_sub_rev] at this
    linarith
  calc walshNorm n J ≤ ρ * ‖T‖ + δ := by linarith
    _ ≤ ρ * (‖J‖ + δ) + δ := by nlinarith
    _ = ρ * ‖J‖ + (ρ + 1) * δ := by ring
    _ = ρ * ‖J‖ + ε := by rw [hδ]; field_simp

