-- Prove2me | solution 1 for MeasureTheory.MemLp.comp_abs_coordinate
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T17:47:15.923129+00:00
-- url     : https://prove2.me/submissions/bd348aa8-6ba5-4d09-9aed-c91ce667427b

import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution (n : ℕ) (p : ℝ≥0∞) (i : Fin n)
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f p (volume.restrict {x | 0 < x i})) :
    MemLp (fun x : EuclideanSpace ℝ (Fin n) =>
      f (WithLp.toLp 2 (fun j => if j = i then |x j| else x j))) p volume := by
  classical
  let H : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < x i}
  have hH : MeasurableSet H :=
    (isOpen_lt continuous_const (EuclideanSpace.proj i).continuous).measurableSet
  let S : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
      if j = i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have hS (x : EuclideanSpace ℝ (Fin n)) (j : Fin n) :
      S x j = if j = i then -x j else x j := by
    by_cases hj : j = i <;> simp [S, LinearIsometryEquiv.piLpCongrRight_apply, hj]
  have hF : MemLp (H.indicator f) p volume :=
    (memLp_indicator_iff_restrict hH).2 hf
  have hsum := hF.add (hF.comp_measurePreserving S.measurePreserving)
  let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := (EuclideanSpace.proj i).toLinearMap
  have hker : L.ker ≠ ⊤ := by
    intro h
    have : EuclideanSpace.single i (1 : ℝ) ∈ L.ker := by rw [h]; trivial
    simpa [L, LinearMap.mem_ker] using this
  have hnull : volume {x : EuclideanSpace ℝ (Fin n) | x i = 0} = 0 :=
    Measure.addHaar_submodule volume L.ker hker
  have hae : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x i ≠ 0 := by
    simpa only [ae_iff, not_not] using hnull
  apply hsum.ae_eq
  filter_upwards [hae] with x hx
  change H.indicator f x + H.indicator f (S x) = _
  by_cases hpos : 0 < x i
  · have hxH : x ∈ H := hpos
    have hsH : S x ∉ H := by simp [H, hS, not_lt.mpr (le_of_lt hpos)]
    have hfold : WithLp.toLp 2 (fun j => if j = i then |x j| else x j) = x := by
      ext j
      by_cases hj : j = i
      · subst j; simp [abs_of_pos hpos]
      · simp [hj]
    simp [Set.indicator_of_mem hxH, Set.indicator_of_notMem hsH, hfold]
  · have hneg : x i < 0 := lt_of_le_of_ne (le_of_not_gt hpos) hx
    have hxH : x ∉ H := hpos
    have hsH : S x ∈ H := by simpa [H, hS] using neg_pos.mpr hneg
    have hfold : WithLp.toLp 2 (fun j => if j = i then |x j| else x j) = S x := by
      ext j
      by_cases hj : j = i
      · subst j; simp [hS, abs_of_neg hneg]
      · simp [hj, hS]
    simp [Set.indicator_of_notMem hxH, Set.indicator_of_mem hsH, hfold]
