-- Prove2me | solution 1 for OAI.Cotype.deletedTail_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:45:13.966762+00:00
-- url     : https://prove2.me/submissions/cd3f162b-b403-483e-8e6a-745cb5a469ea

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

open OAI OAI.Cotype
open scoped BigOperators
variable {m : ℕ}
lemma h51_fsum_sq {ι : Type*} [Fintype ι] [DecidableEq ι] (f : (ι → Bool) → ℝ) {M : ℝ}
    (hf : ∀ x, |f x| ≤ M) (R : Finset (ι → Bool)) :
    (∑ P ∈ R, OAI.Cotype.fourier f P) ^ 2 ≤ M ^ 2 * R.card := by
  set N : ℝ := (Fintype.card (ι → Bool) : ℝ) with hN
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast Fintype.card_pos
  set h : (ι → Bool) → ℝ := fun ε => ∑ P ∈ R, character P ε with hh
  have e1 : ∑ P ∈ R, OAI.Cotype.fourier f P = N⁻¹ * ∑ ε, f ε * h ε := by
    simp only [OAI.Cotype.fourier, average, smul_eq_mul, hh, Finset.mul_sum]
    rw [Finset.sum_comm]
  have e2 : ∑ ε, h ε ^ 2 = N * R.card := by
    simp only [hh, sq, Finset.sum_mul_sum]
    rw [Finset.sum_comm]
    simp_rw [fun P => Finset.sum_comm (s := (Finset.univ : Finset (ι → Bool))) (t := R)
      (f := fun ε Q => character P ε * character Q ε)]
    simp_rw [character_orthogonality]
    simp [Finset.sum_ite_eq, hN, mul_comm]
  have e3 : ∑ ε, f ε ^ 2 ≤ N * M ^ 2 := by
    calc ∑ ε, f ε ^ 2 ≤ ∑ _ε : ι → Bool, M ^ 2 := by
          apply Finset.sum_le_sum; intro ε _
          have := hf ε
          have := abs_nonneg (f ε)
          rw [← sq_abs]; nlinarith
      _ = N * M ^ 2 := by simp [hN]
  have cs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ f h
  rw [e1, mul_pow]
  rw [e2] at cs
  have : (∑ ε, f ε * h ε) ^ 2 ≤ N * M ^ 2 * (N * R.card) :=
    le_trans cs (mul_le_mul_of_nonneg_right e3 (by positivity))
  calc N⁻¹ ^ 2 * (∑ ε, f ε * h ε) ^ 2 ≤ N⁻¹ ^ 2 * (N * M ^ 2 * (N * R.card)) :=
        mul_le_mul_of_nonneg_left this (by positivity)
    _ = M ^ 2 * R.card := by field_simp

lemma h51_card_rect (m k l : ℕ) :
    ((rectangularIndices (ι := Fin m) (κ := Fin m) k l).card : ℝ) ≤ (m : ℝ) ^ (k + l) := by
  have : (rectangularIndices (ι := Fin m) (κ := Fin m) k l).card ≤ m ^ k * m ^ l := by
    unfold rectangularIndices
    refine le_trans Finset.card_image_le ?_
    rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard, Finset.card_univ,
      Fintype.card_fin]
    exact Nat.mul_le_mul (Nat.choose_le_pow _ _) (Nat.choose_le_pow _ _)
  rw [pow_add]; exact_mod_cast this

lemma h51_num (d k l : ℕ) (hd : 4 ≤ d) (hk : d < k) (hl : d < l) :
    (2:ℝ) ^ ((d-2)*(k+l)) * ((1/2:ℝ)^(k*l))^2 ≤ ((1/2:ℝ)^(k+l+5))^2 := by
  rw [one_div_pow, one_div_pow, div_pow, div_pow, one_pow, one_pow, ← pow_mul, ← pow_mul,
    mul_one_div, div_le_div_iff₀ (by positivity) (by positivity), one_mul, ← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  have h1 : (d - 2) + 2 = d := by omega
  have : d * (k + l) + 10 ≤ 2 * (k * l) := by nlinarith
  nlinarith

lemma h51_term {m : ℕ} (f : SignMatrix m → ℝ) {M : ℝ} (hM : 0 ≤ M) (hf : ∀ S, |f S| ≤ M)
    (d k l : ℕ) (hd : 4 ≤ d) (hm : (m : ℝ) ≤ (2 : ℝ)^(d-2)) (hk : d < k) (hl : d < l) :
    |Ckl f k l| * (1/2:ℝ)^(k*l) ≤ M * (1/2:ℝ)^(k+l+5) := by
  have hC : (Ckl f k l) ^ 2 ≤ M ^ 2 * (m : ℝ) ^ (k + l) := by
    have := h51_fsum_sq f hf (rectangularIndices (ι := Fin m) (κ := Fin m) k l)
    unfold Ckl
    exact le_trans this (mul_le_mul_of_nonneg_left (h51_card_rect m k l) (by positivity))
  have hmpow : (m : ℝ) ^ (k + l) ≤ (2:ℝ) ^ ((d-2)*(k+l)) := by
    rw [pow_mul]; exact pow_le_pow_left₀ (by positivity) hm _
  have hsq : (|Ckl f k l| * (1/2:ℝ)^(k*l)) ^ 2 ≤ (M * (1/2:ℝ)^(k+l+5)) ^ 2 := by
    rw [mul_pow, mul_pow, sq_abs]
    calc Ckl f k l ^ 2 * ((1/2:ℝ)^(k*l))^2 ≤ M ^ 2 * (2:ℝ) ^ ((d-2)*(k+l)) * ((1/2:ℝ)^(k*l))^2 := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact le_trans hC (mul_le_mul_of_nonneg_left hmpow (by positivity))
      _ = M ^ 2 * ((2:ℝ) ^ ((d-2)*(k+l)) * ((1/2:ℝ)^(k*l))^2) := by ring
      _ ≤ M ^ 2 * ((1/2:ℝ)^(k+l+5))^2 :=
          mul_le_mul_of_nonneg_left (h51_num d k l hd hk hl) (by positivity)
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq

theorem solution {f : SignMatrix m → ℝ} {M s u : ℝ} {d : ℕ}
    (hM : 0 ≤ M) (hf : ∀ S, |f S| ≤ M) (hd : 4 ≤ d)
    (hm : (m : ℝ) ≤ (2 : ℝ)^(d-2)) (hs : |s| ≤ 1) (hu : |u| ≤ 1) :
    |deletedTail f d s u| ≤ M := by
  unfold deletedTail
  have hterm : ∀ k ∈ Finset.range (m+1), ∀ l ∈ Finset.range (m+1),
      |(if d < k ∧ d < l then Ckl f k l * s^k * u^l * (1/2 : ℝ)^(k*l) else 0)| ≤
        M / 32 * ((1/2:ℝ)^k * (1/2:ℝ)^l) := by
    intro k _ l _
    split_ifs with h
    · rw [abs_mul, abs_mul, abs_mul, abs_pow, abs_pow, abs_of_pos (by positivity : (0:ℝ) < (1/2)^(k*l))]
      have h1 := h51_term f hM hf d k l hd hm h.1 h.2
      have hs' : |s|^k ≤ 1 := pow_le_one₀ (abs_nonneg _) hs
      have hu' : |u|^l ≤ 1 := pow_le_one₀ (abs_nonneg _) hu
      have e : M * (1/2:ℝ)^(k+l+5) = M / 32 * ((1/2:ℝ)^k * (1/2:ℝ)^l) := by
        rw [pow_add, pow_add]; ring
      rw [← e]
      calc |Ckl f k l| * |s| ^ k * |u| ^ l * (1/2:ℝ)^(k*l)
          = (|Ckl f k l| * (1/2:ℝ)^(k*l)) * (|s| ^ k * |u| ^ l) := by ring
        _ ≤ (|Ckl f k l| * (1/2:ℝ)^(k*l)) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_one₀ hs' (by positivity) hu'
        _ ≤ _ := by rw [mul_one]; exact h1
    · simp; positivity
  have hgeo : ∑ k ∈ Finset.range (m+1), (1/2:ℝ)^k ≤ 2 := sum_geometric_two_le _
  calc _ ≤ ∑ k ∈ Finset.range (m+1), |∑ l ∈ Finset.range (m+1),
        (if d < k ∧ d < l then Ckl f k l * s^k * u^l * (1/2 : ℝ)^(k*l) else 0)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ k ∈ Finset.range (m+1), ∑ l ∈ Finset.range (m+1), M / 32 * ((1/2:ℝ)^k * (1/2:ℝ)^l) := by
        apply Finset.sum_le_sum; intro k hk
        exact le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum (fun l hl => hterm k hk l hl))
    _ = M / 32 * ((∑ k ∈ Finset.range (m+1), (1/2:ℝ)^k) * (∑ l ∈ Finset.range (m+1), (1/2:ℝ)^l)) := by
        rw [Finset.sum_mul_sum, Finset.mul_sum]; simp_rw [Finset.mul_sum]
    _ ≤ M / 32 * (2 * 2) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul hgeo hgeo (Finset.sum_nonneg (fun _ _ => by positivity)) (by norm_num)
    _ ≤ M := by nlinarith

