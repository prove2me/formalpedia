-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedContinuousSimplex_diagonal_scaling
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T11:58:42.216277+00:00
-- url     : https://prove2.me/submissions/1cd23a9e-0e26-49a9-bca3-98405921b6ac

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open scoped BigOperators

theorem solution
    (n : Nat) (w : Fin n → Real) (hw : ∀ i, 0 < w i)
    (T : Real) (hT : 0 < T) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T}
      = ENNReal.ofReal (1 / Finset.univ.prod w) *
        MeasureTheory.volume
          {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T} := by
  classical
  let f : (Fin n → Real) →ₗ[Real] (Fin n → Real) :=
    Matrix.toLin' (Matrix.diagonal w)
  let S : Set (Fin n → Real) := {y | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T}
  have hsum : Measurable (fun y : Fin n → Real => ∑ i, y i) := by fun_prop
  have hS : MeasurableSet S := by
    have hset : S =
        (⋂ i : Fin n, {y : Fin n → Real | 0 ≤ y i}) ∩
          {y : Fin n → Real | (∑ i, y i) < T} := by
      ext y
      simp [S]
    rw [hset]
    exact (MeasurableSet.iInter fun i : Fin n =>
      measurableSet_le measurable_const (measurable_pi_apply i)).inter
      (measurableSet_lt hsum measurable_const)
  have hdet : LinearMap.det f = ∏ i : Fin n, w i := by
    simp [f, LinearMap.det_toMatrix']
  have hp : 0 < ∏ i : Fin n, w i := Finset.prod_pos fun i hi => hw i
  have hfd : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact ne_of_gt hp
  have hfx (x : Fin n → Real) : ∀ i, f x i = w i * x i := by
    intro i
    simp [f, Matrix.diagonal_toLin']
  have hpre : f ⁻¹' S =
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T} := by
    ext x
    simp only [Set.mem_preimage, S, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hcoord, hsumx⟩
      refine ⟨?_, ?_⟩
      · intro i
        have hmul : 0 ≤ w i * x i := by simpa [hfx x i] using hcoord i
        exact (mul_nonneg_iff_of_pos_left (hw i)).mp hmul
      · simpa [hfx x] using hsumx
    · rintro ⟨hcoord, hsumx⟩
      refine ⟨?_, ?_⟩
      · intro i
        rw [hfx x i]
        exact mul_nonneg (le_of_lt (hw i)) (hcoord i)
      · simpa [hfx x] using hsumx
  have hfmeas : Measurable f := f.continuous_of_finiteDimensional.measurable
  calc
    MeasureTheory.volume
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i, w i * x i) < T}
      = MeasureTheory.volume (f ⁻¹' S) := by rw [hpre]
    _ = (MeasureTheory.Measure.map f MeasureTheory.volume) S :=
      (MeasureTheory.Measure.map_apply hfmeas hS).symm
    _ = ENNReal.ofReal (1 / Finset.univ.prod w) * MeasureTheory.volume S := by
      have hscale := congrArg
        (fun μ : MeasureTheory.Measure (Fin n → Real) => μ S)
        (Real.map_linearMap_volume_pi_eq_smul_volume_pi hfd)
      simpa [hdet, abs_of_pos hp, one_div, MeasureTheory.Measure.smul_apply, smul_eq_mul] using hscale
    _ = ENNReal.ofReal (1 / Finset.univ.prod w) *
        MeasureTheory.volume
          {y : Fin n → Real | (∀ i, 0 ≤ y i) ∧ (∑ i, y i) < T} := rfl
