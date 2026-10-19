-- Prove2me | solution 1 for OAI.MatchingInterpolation.weights_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T07:02:51.456868+00:00
-- url     : https://prove2.me/submissions/e1fc401b-1588-43e0-870f-b6dd6bc68a3d

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/PolynomialInterpolation.lean:L146-L162
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingInterpolation.weights_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingIncidence
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SpectralContraction
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EquivariantCompression
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialSpaces
import Definitions.Def_OAI_Combinatorics_MatchingPSD_FiberAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ScalarSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeMonomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PartialColorings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableCoordinates
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TablePolynomials
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PermutationSmoothing
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatchingFibers
import Definitions.Def_OAI_Combinatorics_MatchingPSD_GlobalGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_AdmissibleTables
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CutGeometry
import Definitions.Def_OAI_Combinatorics_MatchingPSD_CellAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_SequentialTests
import Definitions.Def_OAI_Combinatorics_MatchingPSD_MatrixAverages
import Definitions.Def_OAI_Combinatorics_MatchingPSD_PolynomialInterpolation

-- ---- from OAI.Combinatorics.MatchingPSD.PolynomialInterpolation ----
namespace OAI

namespace MatchingInterpolation
open Polynomial
open MatchingSmoothing

lemma linePolynomial_eval (d : ℕ) (g : GridIndex d) (v : Point) (t : ℝ) :
    (linePolynomial d g v).eval t = tensorBasis d g (fun a => t * v a) := by
  simp only [linePolynomial, tensorBasis, Polynomial.eval_prod, Polynomial.eval_comp,
    Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  apply Finset.prod_congr rfl
  intro a _
  rw [mul_comm]

lemma linePolynomial_zero (d : ℕ) (g : GridIndex d) (v : Point) :
    (linePolynomial d g v).coeff 0 = ∏ a, (lagrange d (g a)).eval 0 := by
  rw [Polynomial.coeff_zero_eq_eval_zero, linePolynomial_eval]
  simp [tensorBasis]

lemma linePolynomial_one (d : ℕ) (g : GridIndex d) (v : Point) :
    (linePolynomial d g v).coeff 1 =
      ∑ a, v a * ((∏ b ∈ Finset.univ.erase a, (lagrange d (g b)).eval 0) *
        (lagrange d (g a)).derivative.eval 0) := by
  have he (P : ℝ[X]) : P.coeff 1 = P.derivative.eval 0 := by
    simp [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  rw [he, linePolynomial, Polynomial.derivative_prod_finset, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro a _
  simp only [Polynomial.derivative_comp, Polynomial.derivative_mul, Polynomial.derivative_C,
    Polynomial.derivative_X, zero_mul, mul_one, zero_add, Polynomial.eval_mul,
    Polynomial.eval_comp, Polynomial.eval_prod, Polynomial.eval_C, Polynomial.eval_X,
    mul_zero]
  ring

lemma weightPolynomial_zero (d : ℕ) (g : GridIndex d) :
    (weightPolynomial d g).coeff 0 = 0 := by
  simp only [weightPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_smul, smul_eq_mul, linePolynomial_zero]
  ring

lemma weightPolynomial_one (d : ℕ) (g : GridIndex d) :
    (weightPolynomial d g).coeff 1 = 0 := by
  simp only [weightPolynomial, Polynomial.coeff_add, Polynomial.coeff_sub,
    Polynomial.coeff_smul, smul_eq_mul, linePolynomial_one, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, add_zero]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_zero
  intro a _
  fin_cases a <;> simp [dirA, dirB, dirStar, dirP]

lemma weightPolynomial_bound (d : ℕ) (g : GridIndex d) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ t ∈ Set.Icc (0:ℝ) 1,
      |(weightPolynomial d g).eval t| ≤ c * t^2 := by
  have hd : (Polynomial.X^2 : ℝ[X]) ∣ weightPolynomial d g := by
    apply Polynomial.X_pow_dvd_iff.mpr
    intro k hk
    interval_cases k
    · exact weightPolynomial_zero d g
    · exact weightPolynomial_one d g
  obtain ⟨P, hP⟩ := hd
  obtain ⟨b, hb⟩ := (isCompact_Icc : IsCompact (Set.Icc (0:ℝ) 1)).exists_bound_of_continuousOn
    P.continuous.continuousOn
  refine ⟨max b 0, le_max_right _ _, ?_⟩
  intro t ht
  rw [hP, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, abs_mul,
    abs_of_nonneg (sq_nonneg t), mul_comm]
  have htbound : |P.eval t| ≤ b := by simpa only [Real.norm_eq_abs] using hb t ht
  exact mul_le_mul_of_nonneg_right (htbound.trans (le_max_left b 0)) (sq_nonneg t)

lemma weights_bound (d : ℕ) : ∃ c : ℝ, 0 < c ∧ ∀ L : ℝ, 1 ≤ L →
    ∀ g : GridIndex d, |weight d L g| ≤ c / L^2 := by
  classical
  choose c hc hb using weightPolynomial_bound d
  refine ⟨1 + ∑ g, c g, by have hsum := Finset.sum_nonneg (fun g (_ : g ∈ Finset.univ) => hc g); linarith, ?_⟩
  intro L hL g
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have ht : L⁻¹ ∈ Set.Icc (0:ℝ) 1 := ⟨inv_nonneg.mpr hLp.le,
    (inv_le_one₀ hLp).mpr hL⟩
  calc
    |weight d L g| ≤ c g * (L⁻¹)^2 := hb g L⁻¹ ht
    _ ≤ (1+∑ a, c a) * (L⁻¹)^2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      have hh := Finset.single_le_sum (fun a (_ : a ∈ Finset.univ) => hc a)
        (Finset.mem_univ g)
      linarith
    _ = (1+∑ a, c a)/L^2 := by simp [div_eq_mul_inv]

end MatchingInterpolation

end OAI

-- ---- platform node ----
open OAI OAI.MatchingInterpolation
open Polynomial
open MatchingSmoothing


theorem solution : type_of% @_root_.OAI.MatchingInterpolation.weights_bound := @_root_.OAI.MatchingInterpolation.weights_bound
