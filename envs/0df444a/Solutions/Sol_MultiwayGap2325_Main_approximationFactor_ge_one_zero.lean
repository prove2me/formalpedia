-- Prove2me | solution 1 for MultiwayGap2325.Main.approximationFactor_ge_one_zero
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-22T23:20:32.317879+00:00
-- url     : https://prove2.me/submissions/546e7952-9935-4a65-8e56-a6a690155c6a

import Definitions.Def_MultiwayGap2325_Main_RandomCuts

open MeasureTheory Set
open MultiwayGap2325.Main
open scoped BigOperators ENNReal

theorem solution (q : ℕ) (hq : 2 ≤ q) (Ξ : Type) [MeasurableSpace Ξ]
    (P : Measure Ξ) [IsProbabilityMeasure P]
    (C : RandomNonOppositeCut q Ξ P) (α : ℝ) (hα : HasApproximationFactor C α) :
    1 ≤ α := by
  let i : Fin q := ⟨0, by omega⟩
  let j : Fin q := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro h
    have : (0 : ℕ) = 1 := congrArg Fin.val h
    omega
  have hdist : simplexDistance (simplexVertex i) (simplexVertex j) = 1 := by
    simp only [simplexDistance, MultiwayCut.halfL1, simplexVertex, Pi.single_apply]
    have hsum : (∑ x : Fin q, |(if x = i then (1 : ℝ) else 0) -
        if x = j then 1 else 0|) = 2 := by
      rw [← Finset.add_sum_erase Finset.univ
        (fun x : Fin q => |(if x = i then (1 : ℝ) else 0) - if x = j then 1 else 0|)
        (Finset.mem_univ i)]
      simp only [if_pos rfl, if_neg hij, sub_zero, abs_one]
      have hjmem : j ∈ Finset.univ.erase i := by simp [hij, Ne.symm hij]
      rw [← Finset.add_sum_erase (Finset.univ.erase i)
        (fun x : Fin q => |(if x = i then (1 : ℝ) else 0) - if x = j then 1 else 0|) hjmem]
      simp only [Finset.mem_erase, ne_eq, Finset.mem_univ, and_true, if_neg (Ne.symm hij),
        if_pos rfl, zero_sub, abs_neg, abs_one]
      have hz : (∑ x ∈ (Finset.univ.erase i).erase j,
          |(if x = i then (1 : ℝ) else 0) - if x = j then 1 else 0|) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        have hxi : x ≠ i := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hx)).1
        have hxj : x ≠ j := (Finset.mem_erase.mp hx).1
        simp [hxi, hxj]
      rw [hz]
      norm_num
    rw [hsum]
    norm_num
  have hevent : {ξ | C.labeling (ξ, simplexVertex i) ≠ C.labeling (ξ, simplexVertex j)} =
      Set.univ := by
    ext ξ
    simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    have hi := (C.nonOpposite ξ).1 i
    have hj := (C.nonOpposite ξ).1 j
    change C.labeling (ξ, simplexVertex i) = some i at hi
    change C.labeling (ξ, simplexVertex j) = some j at hj
    rw [hi, hj]
    intro h
    exact hij (Option.some.inj h)
  have h := hα (simplexVertex i) (simplexVertex j)
  rw [hevent, hdist, measure_univ, mul_one] at h
  exact ENNReal.one_le_ofReal.mp h
