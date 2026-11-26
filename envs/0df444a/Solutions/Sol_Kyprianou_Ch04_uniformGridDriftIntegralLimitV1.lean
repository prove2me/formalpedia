-- Prove2me | solution 1 for Kyprianou.Ch04.uniformGridDriftIntegralLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:37:35.606557+00:00
-- url     : https://prove2.me/submissions/0cfcc8c5-ab6d-4f3d-86b6-0b34c14c0ee8

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_uniformGridRightClosedCellExistsV1
import Theorems.Thm_Kyprianou_Ch04_uniformGridSingleAtomLimitV1
import Theorems.Thm_Kyprianou_Ch04_uniformGridDriftSumIntegralV1
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- Integrate the bounded strict-left uniform cell approximants by dominated convergence. -/
theorem solution (T : NNReal) (H : NNReal → ℝ) (C : ℝ)
    (hb : ∀ r, |H r| ≤ C)
    (hl : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range (n+1),
      H (T * (i : NNReal) / ((n+1 : ℕ) : NNReal)) *
      ((T * ((i+1 : ℕ) : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal).toReal -
        (T * (i : NNReal) / ((n+1 : ℕ) : NNReal) : NNReal).toReal))
      atTop (𝓝 (∫ s in Icc (0 : ℝ) (T : ℝ), H s.toNNReal)) := by
  let u (n i : ℕ) := T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
  let G (n : ℕ) (s : ℝ) := ∑ i ∈ Finset.range (n+1),
    (Ioc (u n i : ℝ) (u n (i+1) : ℝ)).indicator (fun _ => H (u n i)) s
  let D := Ioc (0 : ℝ) (T : ℝ)
  have hm (n : ℕ) : Measurable (G n) :=
    Finset.measurable_sum _ (fun i _ => measurable_const.indicator measurableSet_Ioc)
  have he (n : ℕ) (s : ℝ) (hs : s ∈ D) :
      G n s = ∑ i ∈ Finset.range (n+1),
        if u n i < s.toNNReal ∧ s.toNNReal ≤ u n (i+1) then H (u n i) else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Set.indicator_apply,mem_Ioc,← NNReal.coe_lt_coe,← NNReal.coe_le_coe,
      Real.coe_toNNReal _ hs.1.le]
  have hlim (s : ℝ) (hs : s ∈ D) :
      Tendsto (fun n => G n s) atTop (𝓝 (H s.toNNReal)) := by
    have hp : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs.1
    have ht : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hs.2
    choose k hk hcell using fun n => Kyprianou.Ch04.uniformGridRightClosedCellExistsV1
      T s.toNNReal hp ht n
    simpa only [he _ s hs,u] using
      Kyprianou.Ch04.uniformGridSingleAtomLimitV1 T s.toNNReal H k hk hcell (hl _ hp)
  have hbound (n : ℕ) (s : ℝ) (hs : s ∈ D) : ‖G n s‖ ≤ C := by
    have hp : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs.1
    have ht : s.toNNReal ≤ T := Real.toNNReal_le_iff_le_coe.mpr hs.2
    obtain ⟨k,hk,hcell⟩ := Kyprianou.Ch04.uniformGridRightClosedCellExistsV1
      T s.toNNReal hp ht n
    rw [he n s hs,Finset.sum_eq_single k]
    · rw [if_pos (show u n k < s.toNNReal ∧ s.toNNReal ≤ u n (k+1) from hcell)]
      exact hb _
    · intro i hi hne
      apply if_neg
      intro h
      apply hne
      apply AvramDividend.Classical.avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
        s.toNNReal (T / ((n+1 : ℕ) : NNReal)) i k
      · simpa [u,div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using h
      · simpa [div_eq_mul_inv,mul_comm,mul_left_comm,mul_assoc] using hcell
    · intro hn
      exact False.elim (hn (Finset.mem_range.mpr hk))
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict D) (F := G) (f := fun s => H s.toNNReal)
    (fun _ => C) (fun n => (hm n).aestronglyMeasurable) (integrable_const C)
    (fun n => (ae_restrict_mem measurableSet_Ioc).mono (hbound n))
    ((ae_restrict_mem measurableSet_Ioc).mono hlim)
  have hEq (n : ℕ) : (∫ s in D,G n s) = ∑ i ∈ Finset.range (n+1),
      H (u n i) * ((u n (i+1) : ℝ) - (u n i : ℝ)) :=
    Kyprianou.Ch04.uniformGridDriftSumIntegralV1 T n H
  rw [integral_Icc_eq_integral_Ioc]
  simpa only [hEq,u,D] using h
