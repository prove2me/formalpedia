-- Prove2me | solution 1 for OAI.Cotype.matrixTwist_row_projection
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:47:08.073693+00:00
-- url     : https://prove2.me/submissions/b76181e4-d78f-49a3-9824-06a8bcb8cf8b

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

open OAI OAI.Cotype
variable {m : ℕ}
lemma h51_avg_xor {n : ℕ} (σ : Cube n) (f : Cube n → ℝ) :
    average (fun ε => f (xorCube σ ε)) = average f := by
  let e : Cube n ≃ Cube n := ⟨xorCube σ, xorCube σ, fun s => by funext j; simp [xorCube],
      fun s => by funext j; simp [xorCube]⟩
  simp only [average, smul_eq_mul]
  congr 1
  exact Equiv.sum_comp e f

lemma h51_avg_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp only [average, smul_eq_mul, ← Finset.mul_sum]; ring

lemma h51_avg_comm {α β : Type*} [Fintype α] [Fintype β] (F : α → β → ℝ) :
    average (fun a => average (fun b => F a b)) = average (fun b => average (fun a => F a b)) := by
  simp only [average, smul_eq_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]; ring

lemma h51_avg_sign {n : ℕ} (i : Fin n) : average (fun ρ : Cube n => sign (ρ i)) = 0 := by
  have h : average (fun ρ : Cube n => sign (ρ i)) = - average (fun ρ : Cube n => sign (ρ i)) := by
    have := h51_avg_xor (fun _ => true) (fun ρ : Cube n => sign (ρ i))
    calc average (fun ρ : Cube n => sign (ρ i))
        = average (fun ε : Cube n => sign (xorCube (fun _ => true) ε i)) := this.symm
      _ = average (fun ε : Cube n => (-1) * sign (ε i)) := by
          congr 1; funext ε; simp [xorCube]
      _ = _ := by rw [h51_avg_mul]; ring
  linarith

lemma h51_avg_split {n : ℕ} (i : Fin n) (G : Bool → ℝ) :
    average (fun ρ : Cube n => sign (ρ i) * G (ρ i)) = (G false - G true) / 2 := by
  have hpt : ∀ ρ : Cube n, sign (ρ i) * G (ρ i) =
      (G false - G true) / 2 + (G false + G true) / 2 * sign (ρ i) := by
    intro ρ; cases ρ i <;> simp [sign] <;> ring
  simp_rw [hpt]
  simp only [average, smul_eq_mul, Finset.sum_add_distrib, ← Finset.mul_sum] at *
  have h0 := h51_avg_sign (n := n) i
  simp only [average, smul_eq_mul] at h0
  have : (Fintype.card (Cube n) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : ∑ x : Cube n, sign (x i) = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (inv_ne_zero this)
    · exact h
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]
  field_simp
  ring

theorem solution (Φ : SignMatrix m → Cube m → Cube m → ℝ)
    (ψ : Cube m → Cube m → ℝ) (a : ℝ)
    (hm : ∀ S δ i, moment ℝ (fun ε => Φ S ε δ) i = a * ψ (fun j => S (i,j)) δ)
    (i : Fin m) (S : SignMatrix m) :
    rowProjection (matrixTwist Φ) i S = a * oddPart (vectorTwist ψ) (fun j => S (i,j)) := by
  set r : Cube m := fun j => S (i,j) with hr
  set G : Bool → ℝ := fun e => average (fun δ : Cube m =>
    ψ (fun j => Bool.xor e (Bool.xor (δ j) (S (i,j)))) δ) with hG
  -- step 1: rewrite inner average via ε = σ ⊕ ρ
  have step1 : ∀ σ : Cube m, average (fun ε => average (fun δ =>
      Φ (dampedSample ε δ (xorCube (rowCube σ) S)) ε δ)) =
      average (fun ρ => average (fun δ => Φ (dampedSample ρ δ S) (xorCube σ ρ) δ)) := by
    intro σ
    rw [← h51_avg_xor σ]
    congr 1; funext ρ; congr 1; funext δ
    congr 1
    funext ij
    simp only [dampedSample, xorCube, rowCube, columnCube]
    cases σ ij.1 <;> cases ρ ij.1 <;> cases δ ij.2 <;> cases S ij <;> rfl
  -- step 2: inner σ-average is a moment
  have step2 : ∀ ρ δ : Cube m, average (fun σ : Cube m => sign (σ i) *
      Φ (dampedSample ρ δ S) (xorCube σ ρ) δ) =
      sign (ρ i) * (a * ψ (fun j => dampedSample ρ δ S (i,j)) δ) := by
    intro ρ δ
    rw [← hm, moment, ← h51_avg_xor ρ, ← h51_avg_mul]
    congr 1; funext τ
    have : xorCube (xorCube ρ τ) ρ = τ := by funext j; simp [xorCube]; cases ρ j <;> cases τ j <;> rfl
    rw [this, smul_eq_mul]
    simp only [xorCube, sign_xor]; ring
  have lhs : rowProjection (matrixTwist Φ) i S = a * ((G false - G true) / 2) := by
    unfold rowProjection matrixTwist
    simp_rw [step1, ← h51_avg_mul]
    rw [h51_avg_comm]
    simp_rw [h51_avg_mul]
    simp_rw [← h51_avg_mul]
    simp_rw [h51_avg_comm (fun σ δ => sign (σ i) * Φ (dampedSample _ δ S) (xorCube σ _) δ)]
    simp_rw [step2]
    rw [← h51_avg_split i G, ← h51_avg_mul]
    congr 1; funext ρ
    rw [hG]; simp only
    rw [← h51_avg_mul, ← h51_avg_mul]
    congr 1; funext δ
    simp only [dampedSample, xorCube, rowCube, columnCube]; ring
  rw [lhs]
  congr 1
  simp only [oddPart, vectorTwist, hG]
  congr 2
  · congr 1; funext δ; congr 1; funext j; simp [xorCube, hr]
  · congr 1; funext δ; congr 1; funext j; simp [xorCube, hr, negateCube]

