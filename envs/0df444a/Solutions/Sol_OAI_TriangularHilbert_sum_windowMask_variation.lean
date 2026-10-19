-- Prove2me | solution 1 for OAI.TriangularHilbert.sum_windowMask_variation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:39:06.226215+00:00
-- url     : https://prove2.me/submissions/78765215-26ff-4832-a7b5-9a2f6b5e0985

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
import Definitions.Def_OAI_Analysis_TriangularHilbert_InitialPlane
import Definitions.Def_OAI_Analysis_TriangularHilbert_TotalJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntWeak
import Definitions.Def_OAI_Analysis_TriangularHilbert_StrongLayer
import Definitions.Def_OAI_Analysis_TriangularHilbert_IntMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_FiniteLineMax
import Definitions.Def_OAI_Analysis_TriangularHilbert_MeshJump
import Definitions.Def_OAI_Analysis_TriangularHilbert_JumpScalar
import Definitions.Def_OAI_Analysis_TriangularHilbert_Switch

open OAI OAI.TriangularHilbert
open scoped BigOperators


theorem solution (t : ℕ → ℝ) (ht : Monotone t) (a b : ℝ) (hab : a ≤ b)
    (A : ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range n, ‖windowMask a b (t (k+1)) A-windowMask a b (t k) A‖) ≤ 2*‖A‖ := by
  classical
  set p : ℕ → ℝ := fun k => if a ≤ t k then 1 else 0 with hp
  set q : ℕ → ℝ := fun k => if b ≤ t k then 1 else 0 with hq
  have hmask : ∀ k, windowMask a b (t k) A = ((p k - q k : ℝ) : ℂ) * A := by
    intro k
    simp only [windowMask, hp, hq]
    by_cases h1 : a ≤ t k <;> by_cases h2 : b ≤ t k <;> simp [h1, h2] <;> (exfalso; push Not at h1; linarith)
  have hstep : ∀ k, ‖windowMask a b (t (k+1)) A - windowMask a b (t k) A‖ ≤
      ((p (k+1) - p k) + (q (k+1) - q k)) * ‖A‖ := by
    intro k
    rw [hmask, hmask, ← sub_mul, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    have hm := ht (Nat.le_succ k)
    simp only [hp, hq]
    by_cases h1 : a ≤ t k <;> by_cases h2 : b ≤ t k <;> by_cases h3 : a ≤ t (k+1) <;> by_cases h4 : b ≤ t (k+1) <;>
      simp [h1, h2, h3, h4] <;> first | linarith | (norm_num) | (exfalso; linarith)
  calc (∑ k ∈ Finset.range n, ‖windowMask a b (t (k+1)) A-windowMask a b (t k) A‖)
      ≤ ∑ k ∈ Finset.range n, ((p (k+1) - p k) + (q (k+1) - q k)) * ‖A‖ := Finset.sum_le_sum (fun k _ => hstep k)
    _ = ((p n - p 0) + (q n - q 0)) * ‖A‖ := by
        rw [← Finset.sum_mul, Finset.sum_add_distrib, Finset.sum_range_sub, Finset.sum_range_sub]
    _ ≤ 2 * ‖A‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        simp only [hp, hq]
        split_ifs <;> norm_num

