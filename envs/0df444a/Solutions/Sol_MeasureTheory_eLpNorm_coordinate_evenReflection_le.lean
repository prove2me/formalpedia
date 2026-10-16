-- Prove2me | solution 1 for MeasureTheory.eLpNorm_coordinate_evenReflection_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-15T17:49:39.768842+00:00
-- url     : https://prove2.me/submissions/2c3bbafa-e995-4a65-ad7b-dba81505d9a1

import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {n : ℕ} (j : Fin n) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hg : AEStronglyMeasurable g (volume.restrict {x | 0 < x j})) :
    eLpNorm (fun x : EuclideanSpace ℝ (Fin n) =>
      g (WithLp.toLp 2 (fun i => if i = j then |x i| else x i))) p volume ≤
      2 * eLpNorm g p (volume.restrict {x | 0 < x j}) := by
  classical
  let H : Set (EuclideanSpace ℝ (Fin n)) := {x | 0 < x j}
  have hH : MeasurableSet H := (isOpen_lt continuous_const (by fun_prop)).measurableSet
  let R : EuclideanSpace ℝ (Fin n) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin n) :=
    LinearIsometryEquiv.piLpCongrRight 2 (fun i =>
      if i = j then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)
  have hR (x : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
      R x i = if i = j then -x i else x i := by
    by_cases hi : i = j <;> simp [R, LinearIsometryEquiv.piLpCongrRight_apply, hi]
  let a := H.indicator g
  have ha : AEStronglyMeasurable a volume :=
    (aestronglyMeasurable_indicator_iff hH).mpr hg
  have hRa : AEStronglyMeasurable (a ∘ R) volume :=
    ha.comp_quasiMeasurePreserving R.measurePreserving.quasiMeasurePreserving
  have hn : ∀ᵐ x : EuclideanSpace ℝ (Fin n) ∂volume, x j ≠ 0 := by
    let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ := (EuclideanSpace.proj j).toLinearMap
    have hker : L.ker ≠ ⊤ := by
      intro h
      have : EuclideanSpace.single j (1 : ℝ) ∈ L.ker := by rw [h]; trivial
      simpa [L, LinearMap.mem_ker] using this
    have hnull : volume {x : EuclideanSpace ℝ (Fin n) | x j = 0} = 0 :=
      Measure.addHaar_submodule volume L.ker hker
    simpa only [ae_iff, not_not] using hnull
  have heq : (fun x : EuclideanSpace ℝ (Fin n) =>
      g (WithLp.toLp 2 (fun i => if i = j then |x i| else x i))) =ᵐ[volume]
      a + a ∘ R := by
    filter_upwards [hn] with x hx
    by_cases ht : 0 < x j
    · have hr : R x ∉ H := by simp [H, hR, not_lt.mpr (neg_nonpos.mpr ht.le)]
      have hxH : x ∈ H := ht
      have he : WithLp.toLp 2 (fun i => if i = j then |x i| else x i) = x := by
        ext i
        by_cases hi : i = j <;> simp [hi, abs_of_pos ht]
      simp [a, he, Set.indicator_of_mem hxH, Set.indicator_of_notMem hr]
    · have ht' : x j < 0 := lt_of_le_of_ne (le_of_not_gt ht) hx
      have hxH : x ∉ H := ht
      have hr : R x ∈ H := by simpa [H, hR] using neg_pos.mpr ht'
      have he : WithLp.toLp 2 (fun i => if i = j then |x i| else x i) = R x := by
        ext i
        by_cases hi : i = j <;> simp [hi, hR, abs_of_neg ht']
      simp [a, he, Set.indicator_of_mem hr, Set.indicator_of_notMem hxH]
  rw [eLpNorm_congr_ae heq]
  calc
    eLpNorm (a + a ∘ R) p volume ≤ eLpNorm a p volume + eLpNorm (a ∘ R) p volume :=
      eLpNorm_add_le ha hRa hp
    _ = 2 * eLpNorm g p (volume.restrict H) := by
      rw [eLpNorm_comp_measurePreserving ha R.measurePreserving,
        eLpNorm_indicator_eq_eLpNorm_restrict hH, two_mul]
