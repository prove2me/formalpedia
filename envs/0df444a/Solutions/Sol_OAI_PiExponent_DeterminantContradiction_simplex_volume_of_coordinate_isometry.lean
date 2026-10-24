-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_of_coordinate_isometry
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T13:00:31.948804+00:00
-- url     : https://prove2.me/submissions/a3433ebb-83eb-4c6a-8f21-8cae1dd83e00

import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_coordinateSplit_preimage_volume
open scoped BigOperators
open MeasureTheory

theorem solution (m : Nat) (T : Real)
    (e : ((Fin m → Real) × Real) ≃ₗᵢ[Real] (Fin (m + 1) → Real))
    (hfirst : ∀ p i, e p (Fin.castSucc i) = p.1 i)
    (hlast : ∀ p, e p (Fin.last m) = p.2) :
    MeasureTheory.volume {x : Fin (m + 1) → Real |
      (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T} =
      MeasureTheory.volume {p : (Fin m → Real) × Real |
        (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ (∑ i, p.1 i) + p.2 < T} := by
  let A : Set (Fin (m + 1) → Real) :=
    {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) < T}
  let B : Set ((Fin m → Real) × Real) :=
    {p | (∀ i, 0 ≤ p.1 i) ∧ 0 ≤ p.2 ∧ (∑ i, p.1 i) + p.2 < T}
  let f : ((Fin m → Real) × Real) → (Fin (m + 1) → Real) :=
    fun p i => Fin.lastCases p.2 p.1 i
  have hset : B = f ⁻¹' A := by
    ext p
    simp only [A, B, Set.mem_setOf_eq, Set.mem_preimage]
    constructor
    · rintro ⟨hp, hp2, hT⟩
      constructor
      · intro i
        refine Fin.lastCases ?_ ?_ i
        · simpa [f] using hp2
        · intro j
          simpa [f] using hp j
      · rw [Fin.sum_univ_castSucc]
        simpa [f] using hT
    · rintro ⟨hp, hT⟩
      constructor
      · intro i
        simpa [f] using hp (Fin.castSucc i)
      · constructor
        · simpa [f] using hp (Fin.last m)
        · rw [Fin.sum_univ_castSucc] at hT
          simpa [f] using hT
  have hA : MeasurableSet A := by
    dsimp [A]
    measurability
  change MeasureTheory.volume A = MeasureTheory.volume B
  rw [hset]
  simpa [A] using
    (OAI.PiExponent.DeterminantContradiction.coordinateSplit_preimage_volume m A hA).symm