-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.weightedSimplex_floor_box_cover_set_inclusion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:09:58.209489+00:00
-- url     : https://prove2.me/submissions/0652506e-435f-4096-8594-91887af751c7

import Definitions.Def_OAI_PiExponent_TruncatedPolynomialJets
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction
open scoped BigOperators

open MeasureTheory Filter Topology in

theorem solution {m : Nat} (w : Fin m → Real) (R : Real) (hw : ∀ i, 0 < w i) (hR : ∑ i : Fin m, w i < R) : {x : Fin m → Real | (∀ i, 0 ≤ x i) ∧ ∑ i, w i * x i ≤ R - ∑ i : Fin m, w i} ⊆ (⋃ n ∈ realWeightedSimplex w R, {x : Fin m → Real | ∀ i, (n i : Real) ≤ x i ∧ x i < (n i : Real) + 1}) := by
  rintro x ⟨hx, hs⟩
  simp only [Set.mem_iUnion, Set.mem_setOf_eq]
  have hfl : ∀ i, ((⌊x i⌋₊ : ℕ) : ℝ) ≤ x i := fun i => Nat.floor_le (hx i)
  have hsum : ∑ i, w i * ((⌊x i⌋₊ : ℕ) : ℝ) ≤ R := by
    have h1 : ∑ i, w i * ((⌊x i⌋₊ : ℕ) : ℝ) ≤ ∑ i, w i * x i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hfl i) (hw i).le
    have h2 : 0 ≤ ∑ i : Fin m, w i := Finset.sum_nonneg fun i _ => (hw i).le
    linarith
  refine ⟨fun i => ⌊x i⌋₊, ?_, fun i => ⟨hfl i, Nat.lt_floor_add_one _⟩⟩
  unfold OAI.PiExponent.realWeightedSimplex
  rw [Finset.mem_filter, Fintype.mem_piFinset]
  refine ⟨fun i => ?_, hsum⟩
  rw [Finset.mem_range, Nat.lt_succ_iff]
  apply Nat.le_floor
  rw [le_div_iff₀ (hw i), mul_comm]
  calc w i * ((⌊x i⌋₊ : ℕ) : ℝ) ≤ ∑ j, w j * ((⌊x j⌋₊ : ℕ) : ℝ) :=
        Finset.single_le_sum (f := fun j => w j * ((⌊x j⌋₊ : ℕ) : ℝ))
          (fun j _ => mul_nonneg (hw j).le (Nat.cast_nonneg _)) (Finset.mem_univ i)
    _ ≤ R := hsum
