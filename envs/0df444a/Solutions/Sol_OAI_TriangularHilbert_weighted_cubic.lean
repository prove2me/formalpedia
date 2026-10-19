-- Prove2me | solution 1 for OAI.TriangularHilbert.weighted_cubic
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T03:37:22.985677+00:00
-- url     : https://prove2.me/submissions/e20cbc6b-eb0d-4427-9379-5b85e1af13a0

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

open OAI OAI.TriangularHilbert
universe uι
open scoped BigOperators
theorem h43_wcs {κ : Type*} (s : Finset κ) (w x y : κ → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * x i * y i) ^ 2 ≤ (∑ i ∈ s, w i * x i ^ 2) * (∑ i ∈ s, w i * y i ^ 2) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun i => Real.sqrt (w i) * x i) (fun i => Real.sqrt (w i) * y i)
  have e1 : ∀ i ∈ s, Real.sqrt (w i) * x i * (Real.sqrt (w i) * y i) = w i * x i * y i := by
    intro i hi; rw [show Real.sqrt (w i) * x i * (Real.sqrt (w i) * y i) = Real.sqrt (w i) ^ 2 * x i * y i by ring,
      Real.sq_sqrt (hw i hi)]
  have e2 : ∀ z : κ → ℝ, ∀ i ∈ s, (Real.sqrt (w i) * z i) ^ 2 = w i * z i ^ 2 := by
    intro z i hi; rw [mul_pow, Real.sq_sqrt (hw i hi)]
  rw [Finset.sum_congr rfl e1, Finset.sum_congr rfl (e2 x), Finset.sum_congr rfl (e2 y)] at h
  exact h

theorem solution {ι : Type uι} (s : Finset ι) (a w : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, a i^2*w i) * Real.sqrt (∑ i ∈ s, a i^2*w i) ≤
      (∑ i ∈ s, a i^3*w i) * Real.sqrt (∑ i ∈ s, w i) := by
  set X := ∑ i ∈ s, a i^2*w i with hXd
  set Y := ∑ i ∈ s, a i^3*w i with hYd
  set Z := ∑ i ∈ s, a i*w i with hZd
  set W := ∑ i ∈ s, w i with hWd
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun i hi => mul_nonneg (sq_nonneg _) (hw i hi)
  have hY0 : 0 ≤ Y := Finset.sum_nonneg fun i hi => mul_nonneg (pow_nonneg (ha i hi) _) (hw i hi)
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun i hi => mul_nonneg (ha i hi) (hw i hi)
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun i hi => hw i hi
  have h1 : X ^ 2 ≤ Y * Z := by
    have h := h43_wcs s w (fun i => a i * Real.sqrt (a i)) (fun i => Real.sqrt (a i)) hw
    have q := fun i (hi : i ∈ s) => Real.sq_sqrt (ha i hi)
    rw [Finset.sum_congr rfl (fun i hi => show w i * (a i * Real.sqrt (a i)) * Real.sqrt (a i) = a i^2*w i by
          rw [show w i * (a i * Real.sqrt (a i)) * Real.sqrt (a i) = w i * a i * Real.sqrt (a i)^2 by ring, q i hi]; ring),
      Finset.sum_congr rfl (fun i hi => show w i * (a i * Real.sqrt (a i))^2 = a i^3*w i by
          rw [mul_pow, q i hi]; ring),
      Finset.sum_congr rfl (fun i hi => show w i * (Real.sqrt (a i))^2 = a i*w i by rw [q i hi]; ring)] at h
    exact h
  have h2 : Z ^ 2 ≤ X * W := by
    have h := h43_wcs s w a (fun _ => 1) hw
    simp only [mul_one, one_pow] at h
    rw [Finset.sum_congr rfl (fun i _ => show w i * a i ^ 2 = a i^2*w i by ring),
      Finset.sum_congr rfl (fun i _ => show w i * a i = a i*w i by ring)] at h
    exact h
  have h3 : X ^ 3 ≤ Y ^ 2 * W := by
    rcases hX0.eq_or_lt with h0 | h0
    · rw [← h0]; simp; positivity
    · have h4 : X ^ 4 ≤ Y ^ 2 * Z ^ 2 := by
        have := pow_le_pow_left₀ (sq_nonneg X) h1 2
        nlinarith [this]
      have h5 : Y ^ 2 * Z ^ 2 ≤ Y ^ 2 * (X * W) := mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
      have h6 : X * X ^ 3 ≤ X * (Y ^ 2 * W) := by nlinarith [h4, h5]
      exact le_of_mul_le_mul_left h6 h0
  have hl : X * Real.sqrt X = Real.sqrt (X ^ 3) := by
    rw [show X ^ 3 = X ^ 2 * X by ring, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hX0]
  have hr : Y * Real.sqrt W = Real.sqrt (Y ^ 2 * W) := by
    rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hY0]
  rw [hl, hr]; exact Real.sqrt_le_sqrt h3

