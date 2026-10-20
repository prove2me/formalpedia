-- Prove2me | solution 1 for OAI.Cotype.chebyshevTruncation_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:42:37.559973+00:00
-- url     : https://prove2.me/submissions/ce01eecd-9dc9-4d20-8241-3265f9144658

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

open OAI OAI.Cotype
open scoped BigOperators
open Polynomial Polynomial.Chebyshev
lemma h51_icos (n : ℤ) : ∫ θ in (0:ℝ)..Real.pi, Real.cos (n * θ) = if n = 0 then Real.pi else 0 := by
  split_ifs with h
  · subst h; simp
  · have hn : (n : ℝ) ≠ 0 := by exact_mod_cast h
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hn, integral_cos]
    simp [Real.sin_int_mul_pi]

lemma h51_orth (j k : ℕ) : ∫ θ in (0:ℝ)..Real.pi, Real.cos ((k:ℝ) * θ) * Real.cos ((j:ℝ) * θ) =
    if k = j then (if j = 0 then Real.pi else Real.pi / 2) else 0 := by
  have hpt : ∀ θ : ℝ, Real.cos ((k:ℝ) * θ) * Real.cos ((j:ℝ) * θ) =
      (Real.cos (((k + j : ℕ) : ℤ) * θ) + Real.cos (((k : ℤ) - j : ℤ) * θ)) / 2 := by
    intro θ
    push_cast
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]; ring
  simp_rw [hpt]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add
    (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _),
    h51_icos, h51_icos]
  by_cases hkj : k = j
  · subst hkj
    by_cases hk : k = 0
    · subst hk; simp
    · simp [hk]
  · have h1 : ((k + j : ℕ) : ℤ) ≠ 0 := by omega
    have h2 : (k : ℤ) - j ≠ 0 := by omega
    have h1' : (k : ℤ) + j ≠ 0 := by omega
    simp [hkj, h1', h2]

lemma h51_coeff {n : ℕ} (c : Fin (n+1) → ℝ) {M : ℝ}
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M) (j : Fin (n+1)) :
    |c j| ≤ 2 * M := by
  have hev : ∀ θ : ℝ, (chebyshevExpansion c).eval (Real.cos θ) =
      ∑ k, c k * Real.cos (((k : ℕ) : ℝ) * θ) := by
    intro θ
    simp only [chebyshevExpansion, Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Polynomial.Chebyshev.T_real_cos]; push_cast; rfl
  set I : ℝ := if (j:ℕ) = 0 then Real.pi else Real.pi / 2 with hI
  have hint : ∫ θ in (0:ℝ)..Real.pi, (chebyshevExpansion c).eval (Real.cos θ) *
      Real.cos (((j : ℕ) : ℝ) * θ) = c j * I := by
    simp_rw [hev, Finset.sum_mul]
    rw [intervalIntegral.integral_finsetSum (fun k _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
    simp_rw [mul_assoc, intervalIntegral.integral_const_mul, h51_orth]
    rw [Finset.sum_eq_single j]
    · simp [hI]
    · intro b _ hb
      have : (b : ℕ) ≠ (j : ℕ) := fun h => hb (Fin.ext h)
      simp [this]
    · simp
  have hbound : ‖∫ θ in (0:ℝ)..Real.pi, (chebyshevExpansion c).eval (Real.cos θ) *
      Real.cos (((j : ℕ) : ℝ) * θ)‖ ≤ M * |Real.pi - 0| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro θ _
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hQ (Real.cos θ) ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩
    have h2 := Real.abs_cos_le_one (((j : ℕ) : ℝ) * θ)
    have h3 := abs_nonneg ((chebyshevExpansion c).eval (Real.cos θ))
    nlinarith
  rw [hint, Real.norm_eq_abs, abs_mul, sub_zero, abs_of_pos Real.pi_pos] at hbound
  have hIge : Real.pi / 2 ≤ |I| := by
    rw [hI]; split_ifs
    · rw [abs_of_pos Real.pi_pos]; linarith [Real.pi_pos]
    · rw [abs_of_pos (by linarith [Real.pi_pos])]
  have hpi := Real.pi_pos
  have hcj := abs_nonneg (c j)
  nlinarith

theorem solution {n : ℕ} (c : Fin (n+1) → ℝ) (d : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(chebyshevTruncation c d).eval x| ≤ 2*M*(d+1) := by
  obtain ⟨θ, rfl⟩ : ∃ θ, Real.cos θ = x := ⟨Real.arccos x, Real.cos_arccos hx.1 hx.2⟩
  simp only [chebyshevTruncation, Polynomial.eval_finsetSum, Polynomial.eval_smul, smul_eq_mul]
  calc |∑ j ∈ Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d), c j * (T ℝ ((j:ℕ):ℤ)).eval (Real.cos θ)|
      ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d), |c j * (T ℝ ((j:ℕ):ℤ)).eval (Real.cos θ)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d), 2 * M := by
        apply Finset.sum_le_sum; intro j _
        rw [abs_mul, Polynomial.Chebyshev.T_real_cos]
        have := Real.abs_cos_le_one ((((j:ℕ):ℤ) : ℝ) * θ)
        have := h51_coeff c hQ j
        have := abs_nonneg (c j)
        nlinarith [abs_nonneg (Real.cos ((((j:ℕ):ℤ) : ℝ) * θ))]
    _ = (Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d)).card * (2 * M) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (d + 1) * (2 * M) := by
        apply mul_le_mul_of_nonneg_right _ (by linarith)
        have : (Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d)).card ≤ (Finset.range (d+1)).card := by
          apply Finset.card_le_card_of_injOn (fun j : Fin (n+1) => (j : ℕ))
          · intro j hj; simp at hj ⊢; omega
          · intro a _ b _ h; exact Fin.ext h
        rw [Finset.card_range] at this
        exact_mod_cast this
    _ = 2 * M * (d + 1) := by ring

