-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weighted_simplex_eq_diagonal_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T07:03:54.86118+00:00
-- url     : https://prove2.me/submissions/334975e3-842f-406b-9e5e-0d73b304a87d

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open Filter Topology
open scoped BigOperators

theorem solution {m : Nat} (w : Fin m → Real) (A : Real)
    (hw : ∀ i, 0 < w i) :
    {x : Fin m → Real | (∀ i : Fin m, 0 ≤ x i) ∧ ∑ i : Fin m, w i * x i ≤ A} =
      (fun x : Fin m → Real => fun i => w i * x i) ⁻¹' {y : Fin m → Real |
        (∀ i : Fin m, 0 ≤ y i) ∧ ∑ i : Fin m, y i ≤ A} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · rintro ⟨hx, hsum⟩
    constructor
    · intro i
      exact mul_nonneg (le_of_lt (hw i)) (hx i)
    · simpa using hsum
  · rintro ⟨hy, hsum⟩
    constructor
    · intro i
      have hwi : w i ≠ 0 := ne_of_gt (hw i)
      have hprod : 0 ≤ (w i)⁻¹ * (w i * x i) :=
        mul_nonneg (inv_nonneg.mpr (le_of_lt (hw i))) (hy i)
      calc
        0 ≤ (w i)⁻¹ * (w i * x i) := hprod
        _ = x i := by field_simp [hwi] <;> ring
    · simpa using hsum