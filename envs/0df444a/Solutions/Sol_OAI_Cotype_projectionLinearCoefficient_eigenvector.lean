-- Prove2me | solution 1 for OAI.Cotype.projectionLinearCoefficient_eigenvector
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:09:21.339658+00:00
-- url     : https://prove2.me/submissions/4dcf2ad9-9a0e-4ff2-a6d1-20ecc57c5db8

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

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem h50e_pp {n : ℕ} (Q : Fin n → X →L[ℝ] X) (c : Fin n → ℝ) (x : X)
    (h : ∀ j, Q j x = c j • x) : projectionProduct Q x = (∏ j, c j) • x := by
  induction n with
  | zero => simp [projectionProduct]
  | succ n ih =>
    simp only [projectionProduct, ContinuousLinearMap.mul_apply]
    rw [ih (fun j => Q j.succ) (fun j => c j.succ) (fun j => h j.succ), map_smul, h 0, smul_smul,
      Fin.prod_univ_succ, mul_comm]

theorem solution {n : ℕ} (P : Fin n → X →L[ℝ] X)
    (p : Cube n) (x : X) (h : ∀ i, P i x = (if p i then (0 : ℝ) else 1) • x) :
    projectionLinearCoefficient P x = ∑ i : Fin n, if p = unitIndex i then x else 0 := by
  classical
  unfold projectionLinearCoefficient
  rw [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hS := h50e_pp (fun j => if decide (j ≠ i) = true then P j else 1)
    (fun j => if j ≠ i then (if p j then (0:ℝ) else 1) else 1) x (fun j => by
      by_cases hj : j = i
      · simp [hj]
      · simp [hj, h j])
  rw [ContinuousLinearMap.mul_apply]
  unfold projectionSubset
  rw [hS, map_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, h i]
  have e : ∀ (c d : ℝ), c • (x - d • x) = (c * (1 - d)) • x := fun c d => by module
  rw [e]
  have hc : (∏ j, if j ≠ i then (if p j then (0:ℝ) else 1) else 1) * (1 - if p i then (0:ℝ) else 1)
      = if p = unitIndex i then 1 else 0 := by
    by_cases hp : p = unitIndex i
    · subst hp
      rw [if_pos rfl]
      have : ∀ j, (if j ≠ i then (if unitIndex i j then (0:ℝ) else 1) else 1) = 1 := by
        intro j; by_cases hj : j = i
        · simp [hj]
        · simp [hj, unitIndex, Ne.symm hj]
      rw [Finset.prod_congr rfl (fun j _ => this j)]; simp [unitIndex]
    · rw [if_neg hp]
      by_cases hpi : p i = true
      · obtain ⟨j, hj⟩ : ∃ j, p j ≠ unitIndex i j := by
          by_contra hc; push Not at hc; exact hp (funext hc)
        have hji : j ≠ i := by
          rintro rfl; simp [unitIndex, hpi] at hj
        have hpj : p j = true := by
          simp [unitIndex, Ne.symm hji] at hj; exact hj
        rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hji, hpj]), zero_mul]
      · simp [hpi]
  rw [hc, ite_smul, one_smul, zero_smul]

