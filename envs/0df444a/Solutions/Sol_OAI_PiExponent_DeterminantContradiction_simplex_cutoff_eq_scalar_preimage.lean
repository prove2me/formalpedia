-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_cutoff_eq_scalar_preimage
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-23T08:07:25.32159+00:00
-- url     : https://prove2.me/submissions/f0d5b328-d65e-4a8e-a15c-9aeb0ceb0977

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open Filter Topology
open scoped BigOperators

theorem solution
    (n : Nat) (r : Real) (hr : 0 ≤ r) (hpos : 0 < r) :
    {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ r} =
      (fun y : Fin n → Real => r⁻¹ • y) ⁻¹'
        {y : Fin n → Real | (∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ 1} := by
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  change
    ((∀ i : Fin n, 0 ≤ y i) ∧ ∑ i : Fin n, y i ≤ r) ↔
      ((∀ i : Fin n, 0 ≤ r⁻¹ * y i) ∧ ∑ i : Fin n, r⁻¹ * y i ≤ 1)
  have hinv : 0 < r⁻¹ := inv_pos.mpr hpos
  constructor
  · rintro ⟨hcoord, hsum⟩
    constructor
    · intro i
      exact mul_nonneg (le_of_lt hinv) (hcoord i)
    · have hsum' : r⁻¹ * (∑ i : Fin n, y i) ≤ r⁻¹ * r :=
        mul_le_mul_of_nonneg_left hsum (le_of_lt hinv)
      calc
        (∑ i : Fin n, r⁻¹ * y i) = r⁻¹ * (∑ i : Fin n, y i) := by
          rw [Finset.mul_sum]
        _ ≤ r⁻¹ * r := hsum'
        _ = 1 := inv_mul_cancel₀ (ne_of_gt hpos)
  · rintro ⟨hcoord, hsum⟩
    constructor
    · intro i
      have hscale : r * (r⁻¹ * y i) = y i := by
        calc
          r * (r⁻¹ * y i) = (r * r⁻¹) * y i := by ring
          _ = y i := by rw [mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
      rw [← hscale]
      exact mul_nonneg (le_of_lt hpos) (hcoord i)
    · have hsum' : r⁻¹ * (∑ i : Fin n, y i) ≤ 1 := by
        simpa only [Finset.mul_sum] using hsum
      calc
        (∑ i : Fin n, y i) = r * (r⁻¹ * (∑ i : Fin n, y i)) := by
          calc
            (∑ i : Fin n, y i) = (r * r⁻¹) * (∑ i : Fin n, y i) := by
              rw [mul_inv_cancel₀ (ne_of_gt hpos), one_mul]
            _ = r * (r⁻¹ * (∑ i : Fin n, y i)) := by ring
        _ ≤ r * 1 := mul_le_mul_of_nonneg_left hsum' (le_of_lt hpos)
        _ = r := mul_one r