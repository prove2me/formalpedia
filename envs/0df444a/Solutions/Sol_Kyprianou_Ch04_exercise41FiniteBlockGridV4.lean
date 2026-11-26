-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41FiniteBlockGridV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:41:51.861589+00:00
-- url     : https://prove2.me/submissions/20eeca1a-635f-4e4f-8bbd-7caa4ae56f0e

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise41FiniteGridOccupancyV3
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Classical
set_option autoImplicit false
open Kyprianou.Ch04
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F)
    (I : Finset ℕ) (D : ℕ → Finset NNReal) (a δ : NNReal) (h : ℝ)
    (hh : 0 < h) (hd : 0 < L.drift)
    (hBlock : ∀ i ∈ I, ∀ t ∈ D i, a ≤ t ∧ t < a + δ)
    (hcell : ∀ i ∈ I, ∀ t ∈ D i,
      (a : ℝ) + (i : ℝ) * h ≤ (t : ℝ) ∧
      (t : ℝ) < (a : ℝ) + ((i : ℝ) + 1) * h) :
    let A : ℕ → Set Ω := fun i =>
      {ω | ∃ t ∈ D i, |L.X t ω| < L.drift * h / 8}
    let p := P {ω | ∀ u : NNReal, 0 < u → u ≤ δ →
      L.drift / 2 * (u : ℝ) ≤ L.X u ω}
    (∀ i ∈ I, MeasurableSet (A i)) ∧ p * ∑ i ∈ I, P (A i) ≤ 2 := by
  let U := I.biUnion D
  let R := (Finset.image₂ (fun s t : NNReal => t - s) U U).filter
    (fun u => 0 < u ∧ u ≤ δ)
  apply exercise41FiniteGridOccupancyV3 P F L I D
    (fun _ => a + δ) R δ (a : ℝ) h hh hd
  · intro i hi t ht
    exact (hBlock i hi t ht).2.le
  · exact hcell
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro i hi j hj hij s hs t ht
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_image₂_of_mem (Finset.mem_biUnion.mpr ⟨i, hi, hs⟩)
      (Finset.mem_biUnion.mpr ⟨j, hj, ht⟩), ?_⟩
    have hidx : (i : ℝ) + 1 ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hij
    have hsi := hcell i hi s hs
    have htj := hcell j hj t ht
    have hst : (s : ℝ) < (t : ℝ) := by nlinarith
    have hst' : s < t := by exact_mod_cast hst
    have hsa := (hBlock i hi s hs).1
    have hta := (hBlock j hj t ht).2
    refine ⟨tsub_pos_of_lt hst', ?_⟩
    apply tsub_le_iff_right.mpr
    exact hta.le.trans (by simpa only [add_comm] using add_le_add_right hsa δ)
