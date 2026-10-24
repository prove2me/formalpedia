-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_cutoff_volume_measure_scaling_zero
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:16:11.847315+00:00
-- url     : https://prove2.me/submissions/8cf77641-923f-4d48-b0b3-78487baed219

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution (n : Nat) :
    MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
      ∑ i : Fin n, y i ≤ 0} =
      ENNReal.ofReal (0 ^ n) *
        MeasureTheory.volume {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧
          ∑ i : Fin n, y i ≤ 1} := by
  by_cases hn : n = 0
  · subst n
    simp
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    haveI : Nonempty (Fin n) := ⟨⟨0, hnpos⟩⟩
    let S : Set (Fin n → Real) := {y | (∀ i : Fin n, 0 ≤ y i) ∧
      ∑ i : Fin n, y i ≤ 0}
    have hS : S = {0} := by
      ext y
      constructor
      · rintro ⟨hy, hsum⟩
        have hi (i : Fin n) : y i = 0 := by
          have hle : y i ≤ ∑ j : Fin n, y j := by
            simpa using (Finset.single_le_sum
              (s := Finset.univ) (fun j hj => hy j) (Finset.mem_univ i))
          exact le_antisymm (le_trans hle hsum) (hy i)
        have hy0 : y = 0 := funext hi
        simp [hy0]
      · intro hy
        change y = 0 at hy
        subst y
        change (∀ i : Fin n, 0 ≤ (0 : Fin n → Real) i) ∧
          (∑ i : Fin n, (0 : Fin n → Real) i) ≤ 0
        constructor
        · intro i
          exact le_rfl
        · simp
    change MeasureTheory.volume S = _
    have hzero : ENNReal.ofReal (0 ^ n) = 0 := by
      rw [zero_pow (Nat.ne_of_gt hnpos)]
      simp
    rw [hS, hzero]
    simp
