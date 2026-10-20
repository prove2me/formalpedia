-- Prove2me | solution 1 for OAI.Cotype.row_rectangle_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:49:24.500983+00:00
-- url     : https://prove2.me/submissions/065ef841-e8d0-421c-9f20-866e8bc48175

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

open OAI OAI.Cotype
open scoped BigOperators
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
lemma h51_gavg_xor {α : Type*} [Fintype α] [DecidableEq α] (σ : α → Bool) (f : (α → Bool) → ℝ) :
    average (fun ε => f (xorCube σ ε)) = average f := by
  let e : (α → Bool) ≃ (α → Bool) := ⟨xorCube σ, xorCube σ, fun s => by funext j; simp [xorCube],
      fun s => by funext j; simp [xorCube]⟩
  simp only [average, smul_eq_mul]
  congr 1
  exact Equiv.sum_comp e f

lemma h51_gavg_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    average (fun x => c * f x) = c * average f := by
  simp only [average, smul_eq_mul, ← Finset.mul_sum]; ring

lemma h51_gavg_comm {α β : Type*} [Fintype α] [Fintype β] (F : α → β → ℝ) :
    average (fun a => average (fun b => F a b)) = average (fun b => average (fun a => F a b)) := by
  simp only [average, smul_eq_mul, ← Finset.mul_sum]
  rw [Finset.sum_comm]; ring

lemma h51_gavg_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    average (fun _ : α => c) = c := by
  simp only [average, smul_eq_mul, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

lemma h51_neg_char {ι : Type*} [Fintype ι] [DecidableEq ι] (p ε : ι → Bool) :
    character p (negateCube ε) = paritySign p * character p ε := by
  unfold character paritySign negateCube
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  cases p i <;> cases ε i <;> simp

lemma h51_odd_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) (hf : IsOdd f)
    (p : ι → Bool) (hp : paritySign p = 1) : OAI.Cotype.fourier f p = 0 := by
  have h : OAI.Cotype.fourier f p = - OAI.Cotype.fourier f p := by
    unfold OAI.Cotype.fourier
    calc average (fun ε => f ε * character p ε)
        = average (fun ε => f (xorCube (fun _ => true) ε) * character p (xorCube (fun _ => true) ε)) :=
          (h51_gavg_xor (fun _ => true) (fun ε => f ε * character p ε)).symm
      _ = average (fun ε => (-1) * (f ε * character p ε)) := by
          congr 1; funext ε
          have : xorCube (fun _ => true) ε = negateCube ε := by funext j; simp [xorCube, negateCube]
          rw [this, hf, h51_neg_char, hp]; ring
      _ = _ := by rw [h51_gavg_mul]; ring
  linarith

-- marginal: averaging a function of row i
lemma h51_marginal {m n : ℕ} (i : Fin m) (F : Cube n → ℝ) :
    average (fun S : (Fin m × Fin n) → Bool => F (fun j => S (i,j))) = average F := by
  classical
  have h1 : ∀ r : Cube n, average (fun S : (Fin m × Fin n) → Bool => F (fun j => S (i,j))) =
      average (fun S : (Fin m × Fin n) → Bool => F (xorCube r (fun j => S (i,j)))) := by
    intro r
    rw [← h51_gavg_xor (fun ab : Fin m × Fin n => decide (ab.1 = i) && r ab.2)]
    congr 1; funext S; congr 1; funext j; simp [xorCube]
  calc average (fun S : (Fin m × Fin n) → Bool => F (fun j => S (i,j)))
      = average (fun r : Cube n => average (fun S : (Fin m × Fin n) → Bool =>
          F (xorCube (fun j => S (i,j)) r))) := by
        rw [← h51_gavg_const (α := Cube n) (average (fun S : (Fin m × Fin n) → Bool => F (fun j => S (i,j))))]
        congr 1; funext r; rw [h1 r]
        congr 1; funext S; congr 1; funext j; simp [xorCube, Bool.xor_comm]
    _ = average (fun S : (Fin m × Fin n) → Bool => average (fun r : Cube n =>
          F (xorCube (fun j => S (i,j)) r))) := h51_gavg_comm _
    _ = average F := by
        rw [← h51_gavg_const (α := (Fin m × Fin n) → Bool) (average F)]
        congr 1; funext S
        exact h51_gavg_xor _ F

lemma h51_char_rect {m n : ℕ} (i : Fin m) (t : Finset (Fin n)) (S : (Fin m × Fin n) → Bool) :
    character (rectangle {i} t) S = character (setIndex t) (fun j => S (i,j)) := by
  unfold character rectangle setIndex
  rw [Fintype.prod_prod_type, Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · simp

lemma h51_par_rect {m n : ℕ} (i : Fin m) (t : Finset (Fin n)) :
    paritySign (rectangle {i} t) = (-1) ^ t.card := by
  unfold paritySign rectangle
  rw [Fintype.prod_prod_type, Finset.prod_eq_single i]
  · simp [Finset.prod_ite_mem]
  · intro b _ hb; simp [hb]
  · simp

lemma h51_par_set {n : ℕ} (t : Finset (Fin n)) : paritySign (setIndex t) = (-1) ^ t.card := by
  unfold paritySign setIndex
  simp [Finset.prod_ite_mem]

lemma h51_char_shift {n : ℕ} (t : Finset (Fin n)) (b : Bool) (r : Cube n) :
    character (setIndex t) (fun j => Bool.xor b (r j)) = sign b ^ t.card * character (setIndex t) r := by
  unfold character setIndex
  simp only [decide_eq_true_eq, sign_xor]
  rw [Fintype.prod_ite_mem, Fintype.prod_ite_mem, Finset.prod_mul_distrib, Finset.prod_const]

theorem solution {m n : ℕ} {Ψ : ((Fin m × Fin n) → Bool) → ℝ}
    {g : Cube n → ℝ} {a : ℝ} (hΨ : IsOdd Ψ) (hg : IsOdd g)
    (hp : ∀ (i : Fin m) S, average (fun σ : Cube m =>
      sign (σ i) * Ψ (xorCube (rowCube σ) S)) = a * g (fun j => S (i,j)))
    (i : Fin m) (t : Finset (Fin n)) :
    fourier Ψ (rectangle {i} t) = a * fourier g (setIndex t) := by
  rcases Nat.even_or_odd t.card with he | ho
  · have h1 : OAI.Cotype.fourier Ψ (rectangle {i} t) = 0 :=
      h51_odd_zero Ψ hΨ _ (by rw [h51_par_rect, he.neg_one_pow])
    have h2 : OAI.Cotype.fourier g (setIndex t) = 0 :=
      h51_odd_zero g hg _ (by rw [h51_par_set, he.neg_one_pow])
    rw [h1, h2, mul_zero]
  · -- a ĝ(t) = E_S rowProj(S) χ(S_i)
    have hsq : ∀ σ : Cube m, sign (σ i) * sign (σ i) ^ t.card = 1 := by
      intro σ
      obtain ⟨k, hk⟩ := ho
      rw [hk, ← pow_succ', show 2 * k + 1 + 1 = 2 * (k + 1) by ring, pow_mul]
      have : sign (σ i) ^ 2 = 1 := by rw [sq, sign_sq]
      rw [this, one_pow]
    symm
    calc a * OAI.Cotype.fourier g (setIndex t)
        = average (fun S : (Fin m × Fin n) → Bool =>
            a * g (fun j => S (i,j)) * character (setIndex t) (fun j => S (i,j))) := by
          unfold OAI.Cotype.fourier
          rw [← h51_gavg_mul, ← h51_marginal i]
          congr 1; funext S; ring
      _ = average (fun S : (Fin m × Fin n) → Bool => average (fun σ : Cube m =>
            sign (σ i) * Ψ (xorCube (rowCube σ) S) * character (setIndex t) (fun j => S (i,j)))) := by
          congr 1; funext S
          rw [← hp i S, mul_comm, ← h51_gavg_mul]
          congr 1; funext σ; ring
      _ = average (fun σ : Cube m => average (fun S : (Fin m × Fin n) → Bool =>
            sign (σ i) * Ψ (xorCube (rowCube σ) S) * character (setIndex t) (fun j => S (i,j)))) :=
          h51_gavg_comm _
      _ = average (fun σ : Cube m => OAI.Cotype.fourier Ψ (rectangle {i} t)) := by
          congr 1; funext σ
          rw [← h51_gavg_xor (rowCube σ : (Fin m × Fin n) → Bool)]
          unfold OAI.Cotype.fourier
          rw [← one_mul (average _), ← hsq σ, mul_assoc, ← h51_gavg_mul, ← h51_gavg_mul]
          congr 1; funext S
          have e1 : xorCube (rowCube σ : (Fin m × Fin n) → Bool) (xorCube (rowCube σ) S) = S := by
            funext ab; simp [xorCube]
          rw [e1, h51_char_rect]
          have e2 : (fun j => xorCube (rowCube σ : (Fin m × Fin n) → Bool) S (i,j)) =
              (fun j => Bool.xor (σ i) (S (i,j))) := by
            funext j; simp [xorCube, rowCube]
          rw [e2, h51_char_shift]
          have h2 : sign (σ i) ^ 2 * sign (σ i) ^ (t.card * 2) = 1 := by
            have h := hsq σ
            calc _ = (sign (σ i) * sign (σ i) ^ t.card) ^ 2 := by ring
              _ = 1 := by rw [h]; norm_num
          linear_combination (Ψ S * character (setIndex t) (fun j => S (i,j))) * h2
      _ = _ := h51_gavg_const _

