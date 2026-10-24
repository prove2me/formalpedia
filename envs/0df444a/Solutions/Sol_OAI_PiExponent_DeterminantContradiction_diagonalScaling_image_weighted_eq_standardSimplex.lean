-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.diagonalScaling_image_weighted_eq_standardSimplex
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T15:04:05.026562+00:00
-- url     : https://prove2.me/submissions/1ea639a4-d424-411f-b9cc-f5f1de716c67

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) (hA : 0 ≤ A) :
    (fun x : Fin m → Real => fun i => w i * x i) ''
        {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A} =
      {y : Fin m → Real | (∀ i, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A} := by
  ext y
  change (∃ x : Fin m → Real,
      x ∈ {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A} ∧
        (fun x : Fin m → Real => fun i => w i * x i) x = y) ↔
    ((∀ i, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A)
  constructor
  · rintro ⟨x, hx, hxy⟩
    change (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A at hx
    rcases hx with ⟨hx_nonneg, hx_sum⟩
    refine ⟨?_, ?_⟩
    · intro i
      rw [← congrFun hxy i]
      exact mul_nonneg (le_of_lt (hw i)) (hx_nonneg i)
    · calc
        (∑ i : Fin m, y i) = ∑ i : Fin m, w i * x i := by
          apply Finset.sum_congr rfl
          intro i hi
          exact (congrFun hxy i).symm
        _ ≤ A := hx_sum
  · rintro ⟨hy_nonneg, hy_sum⟩
    let x : Fin m → Real := fun i => y i / w i
    have hx_nonneg : ∀ i, 0 ≤ x i := by
      intro i
      dsimp [x]
      exact div_nonneg (hy_nonneg i) (le_of_lt (hw i))
    have hxy : (fun i => w i * x i) = y := by
      funext i
      dsimp [x]
      field_simp [ne_of_gt (hw i)]
    refine ⟨x, ?_, hxy⟩
    change (∀ i, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A
    refine ⟨hx_nonneg, ?_⟩
    calc
      (∑ i : Fin m, w i * x i) = ∑ i : Fin m, y i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact congrFun hxy i
      _ ≤ A := hy_sum