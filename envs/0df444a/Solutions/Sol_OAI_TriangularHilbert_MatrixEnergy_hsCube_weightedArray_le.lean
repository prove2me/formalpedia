-- Prove2me | solution 1 for OAI.TriangularHilbert.MatrixEnergy.hsCube_weightedArray_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:58:46.218991+00:00
-- url     : https://prove2.me/submissions/5ee482aa-4491-487a-aef7-be9a21aebd74

import Mathlib
import Definitions.Def_TriangularHilbert
import Definitions.Def_OAI_Analysis_TriangularHilbert_Gaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshMass
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianMoments
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedWindowScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_MatrixSupport
import Definitions.Def_OAI_Analysis_TriangularHilbert_Support
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedGram
import Definitions.Def_OAI_Analysis_TriangularHilbert_WeightedStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_GroupedGaussian
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatCost
import Definitions.Def_OAI_Analysis_TriangularHilbert_NormBounds
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatInsert
import Definitions.Def_OAI_Analysis_TriangularHilbert_GaussianDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneChart
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDom
import Definitions.Def_OAI_Analysis_TriangularHilbert_HeatBound
import Definitions.Def_OAI_Analysis_TriangularHilbert_GramDeriv
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneIntegral
import Definitions.Def_OAI_Analysis_TriangularHilbert_PlaneDissipation
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedTraceOrder
import Definitions.Def_OAI_Analysis_TriangularHilbert_MassPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_SignedConvolution
import Definitions.Def_OAI_Analysis_TriangularHilbert_RankJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_ZeroStar
import Definitions.Def_OAI_Analysis_TriangularHilbert_StarJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialAlgebra

open OAI OAI.TriangularHilbert OAI.TriangularHilbert.MatrixEnergy
universe uι
open scoped Matrix MatrixOrder ComplexOrder Matrix.Norms.L2Operator BigOperators
variable {ι : Type uι} [Fintype ι]


theorem solution (A : Three → Matrix ι ι ℂ) (g : Three → ι → ℝ)
    (hg : ∀ v i, 0 ≤ g v i) {M : ℝ} (hM : 0 ≤ M)
    (hm : ∀ v, (∑ i, g v i) ≤ M) (v : Three) :
    hsCube (weightedArray A g v) ≤ M * ∑ i, ∑ j, ‖A v i j‖^3 * (g v i*g (v+1) j) := by
  set μ : ι → ι → ℝ := fun i j => g v i * g (v+1) j with hμ
  have hμ0 : ∀ i j, 0 ≤ μ i j := fun i j => mul_nonneg (hg _ _) (hg _ _)
  have hS : hsSquare (weightedArray A g v) = ∑ i, ∑ j, ‖A v i j‖^2 * μ i j := by
    unfold hsSquare weightedArray
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg (Real.sqrt_nonneg _)]
    have h1 := Real.sq_sqrt (hg v i)
    have h2 := Real.sq_sqrt (hg (v+1) j)
    simp only [hμ]
    rw [mul_pow, mul_pow, h1, h2]; ring
  set S := ∑ i, ∑ j, ‖A v i j‖^2 * μ i j with hSdef
  set T := ∑ i, ∑ j, ‖A v i j‖^3 * μ i j with hTdef
  have hmass : (∑ i, ∑ j, μ i j) ≤ M^2 := by
    have : (∑ i, ∑ j, μ i j) = (∑ i, g v i) * (∑ j, g (v+1) j) := by
      rw [Finset.sum_mul_sum]
    rw [this, sq]
    exact mul_le_mul (hm v) (hm (v+1)) (Finset.sum_nonneg (fun j _ => hg _ _)) hM
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hμ0 i j)))
  have hT0 : 0 ≤ T := Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => mul_nonneg (by positivity) (hμ0 i j)))
  unfold hsCube
  rw [hS]
  change S * Real.sqrt S ≤ M * T
  rcases hS0.eq_or_lt with h0 | hSpos
  · rw [← h0]; simp; exact mul_nonneg hM hT0
  rcases hM.eq_or_lt with hM0 | hMpos
  · exfalso
    have : (∑ i, ∑ j, μ i j) ≤ 0 := by rw [← hM0] at hmass; simpa using hmass
    have hz : ∀ i j, μ i j = 0 := by
      intro i j
      have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hμ0 i j))).mp
        (le_antisymm this (Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hμ0 i j)))) i (Finset.mem_univ _)
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hμ0 i j)).mp h1 j (Finset.mem_univ _)
    have : S = 0 := by simp [hSdef, hz]
    linarith
  set r := Real.sqrt S with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hSpos
  have hrr : r * r = S := Real.mul_self_sqrt hS0
  set l := r / M with hl
  have hl0 : 0 < l := div_pos hr0 hMpos
  have hpt : ∀ i j, 3 * l * (‖A v i j‖^2 * μ i j) ≤ 2 * (‖A v i j‖^3 * μ i j) + l^3 * μ i j := by
    intro i j
    have hx := norm_nonneg (A v i j)
    have : 3 * l * ‖A v i j‖^2 ≤ 2 * ‖A v i j‖^3 + l^3 := by
      nlinarith [mul_nonneg (sq_nonneg (‖A v i j‖ - l)) (by linarith : (0:ℝ) ≤ 2*‖A v i j‖ + l)]
    nlinarith [hμ0 i j]
  have hsum : 3 * l * S ≤ 2 * T + l^3 * (∑ i, ∑ j, μ i j) := by
    rw [hSdef, hTdef, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun i _ => ?_)
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => hpt i j)
  have hl3 : l^3 * (∑ i, ∑ j, μ i j) ≤ l^3 * M^2 := mul_le_mul_of_nonneg_left hmass (by positivity)
  have hlM : l * M = r := by rw [hl]; field_simp
  have key : 3 * l * S ≤ 2 * T + l * S := by
    have : l^3 * M^2 = l * S := by rw [← hrr, ← hlM]; ring
    linarith
  have : l * S ≤ T := by linarith
  have : S * r = M * (l * S) := by rw [← hlM]; ring
  rw [this]
  exact mul_le_mul_of_nonneg_left ‹l * S ≤ T› hM

