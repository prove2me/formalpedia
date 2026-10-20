-- Prove2me | solution 2 for OAI.Cotype.chebyshevTruncation_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T23:54:36.782693+00:00
-- url     : https://prove2.me/submissions/687fbae6-336d-4d7e-85f9-fdaf5168cb78

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Cotype/ChebyshevTruncation.lean:L25-L44
-- (upload_full_project.md Phase 4): solution for node OAI.Cotype.chebyshevTruncation_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
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

-- ---- from OAI.Analysis.Cotype.ChebyshevBounds ----
namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Chebyshev MeasureTheory
namespace Cotype

theorem chebyshev_abs_le_one (n : ℕ) {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(T ℝ n).eval x| ≤ 1 := by
  rw [← Real.cos_arccos hx.1 hx.2, T_real_cos]
  exact Real.abs_cos_le_one _

theorem chebyshev_pairing_bound (Q : ℝ[X]) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |Q.eval x| ≤ M) :
    |∫ x, Q.eval x * (T ℝ n).eval x ∂measureT| ≤ M * Real.pi := by
  rw [integral_measureT_eq_integral_cos]
  have hh : ∀ θ ∈ Set.uIoc (0 : ℝ) Real.pi,
      ‖Q.eval (Real.cos θ) * (T ℝ n).eval (Real.cos θ)‖ ≤ M := by
    intro θ _
    rw [Real.norm_eq_abs, abs_mul, T_real_cos]
    exact (mul_le_mul (hQ _ ⟨Real.neg_one_le_cos θ, Real.cos_le_one θ⟩)
      (Real.abs_cos_le_one _) (abs_nonneg _) hM).trans_eq (mul_one M)
  simpa [Real.norm_eq_abs, abs_of_pos Real.pi_pos] using
    intervalIntegral.norm_integral_le_of_norm_le_const hh

theorem chebyshev_pairing (i j : ℕ) :
    (∫ x, (T ℝ i).eval x * (T ℝ j).eval x ∂measureT) =
      if i = j then (if j = 0 then Real.pi else Real.pi/2) else 0 := by
  by_cases hij : i = j
  · subst i
    by_cases hj : j = 0
    · subst j
      simpa using integral_eval_T_real_mul_self_measureT_zero
    · simpa [hj] using integral_T_real_mul_self_measureT_of_ne_zero hj
  · simpa [hij] using integral_eval_T_real_mul_eval_T_real_measureT_of_ne hij

theorem chebyshevExpansion_pairing {d : ℕ} (c : Fin (d+1) → ℝ) (j : Fin (d+1)) :
    (∫ x, (chebyshevExpansion c).eval x * (T ℝ (j : ℕ)).eval x ∂measureT) =
      c j * (if (j : ℕ) = 0 then Real.pi else Real.pi/2) := by
  simp only [chebyshevExpansion, eval_finsetSum, eval_smul, smul_eq_mul, Finset.sum_mul]
  rw [MeasureTheory.integral_finsetSum]
  · simp_rw [mul_assoc, MeasureTheory.integral_const_mul, chebyshev_pairing]
    simp only [Fin.val_inj]
    simp
  · intro i _
    exact integrable_measureT (by fun_prop)

theorem chebyshevExpansion_coefficient_bound {d : ℕ} (c : Fin (d+1) → ℝ)
    {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M)
    (j : Fin (d+1)) : |c j| ≤ 2*M := by
  have hh := chebyshev_pairing_bound (chebyshevExpansion c) j hM hQ
  rw [chebyshevExpansion_pairing, abs_mul] at hh
  split_ifs at hh
  · rw [abs_of_pos Real.pi_pos] at hh
    nlinarith [Real.pi_pos]
  · rw [abs_of_pos (by positivity : 0 < Real.pi/2)] at hh
    nlinarith [Real.pi_pos]

end Cotype

end

end OAI

-- ---- from OAI.Analysis.Cotype.ChebyshevTruncation ----
namespace OAI

noncomputable section
open scoped BigOperators
open Polynomial Polynomial.Chebyshev
namespace Cotype

theorem card_low_indices_le (n d : ℕ) :
    (Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d)).card ≤ d+1 := by
  let s := Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d)
  have hsub : s.image Fin.val ⊆ Finset.range (d+1) := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hi
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hj).2)
  calc
    s.card = (s.image Fin.val).card := (Finset.card_image_of_injective _ Fin.val_injective).symm
    _ ≤ (Finset.range (d+1)).card := Finset.card_le_card hsub
    _ = d+1 := Finset.card_range _

theorem chebyshevTruncation_bound {n : ℕ} (c : Fin (n+1) → ℝ) (d : ℕ)
    {M : ℝ} (hM : 0 ≤ M)
    (hQ : ∀ x ∈ Set.Icc (-1) 1, |(chebyshevExpansion c).eval x| ≤ M)
    {x : ℝ} (hx : x ∈ Set.Icc (-1) 1) :
    |(chebyshevTruncation c d).eval x| ≤ 2*M*(d+1) := by
  simp only [chebyshevTruncation, eval_finsetSum, eval_smul, smul_eq_mul]
  calc
    _ ≤ ∑ j ∈ Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d),
        |c j * (T ℝ (j : ℕ)).eval x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d), 2*M := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      exact (mul_le_mul (chebyshevExpansion_coefficient_bound c hM hQ j)
        (chebyshev_abs_le_one j hx) (abs_nonneg _) (by positivity)).trans_eq (mul_one _)
    _ ≤ 2*M*(d+1) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : ((Finset.univ.filter (fun j : Fin (n+1) => (j : ℕ) ≤ d)).card : ℝ) ≤ d+1 := by
        exact_mod_cast card_low_indices_le n d
      nlinarith

end Cotype

end

end OAI

-- ---- platform node ----
open OAI OAI.Cotype
open scoped BigOperators
open Polynomial Polynomial.Chebyshev


theorem solution : type_of% @_root_.OAI.Cotype.chebyshevTruncation_bound := @_root_.OAI.Cotype.chebyshevTruncation_bound
