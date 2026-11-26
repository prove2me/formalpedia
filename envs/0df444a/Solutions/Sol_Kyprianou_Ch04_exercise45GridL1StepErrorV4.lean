-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45GridL1StepErrorV4
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:38:31.635603+00:00
-- url     : https://prove2.me/submissions/926d178a-9e19-4890-82d4-e49bfecfa43b

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_uniformGridRightClosedCellExistsV1
import Theorems.Thm_Kyprianou_Ch04_uniformGridSingleAtomLimitV1
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_uniform_halfopen_cell_unique_index
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal Classical Topology
set_option autoImplicit false
theorem solution
    (T : NNReal) (H : NNReal → ℝ) (C : ℝ)
    (hb : ∀ r, |H r| ≤ C)
    (hl : ∀ r, 0 < r → Tendsto H (𝓝[<] r) (𝓝 (H r))) :
    let u : ℕ → ℕ → NNReal := fun n i => T * (i : NNReal) / ((n+1 : ℕ) : NNReal)
    let G : ℕ → ℝ → ℝ := fun n s => ∑ i ∈ Finset.range (n+1),
      (Ioc (u n i : ℝ) (u n (i+1) : ℝ)).indicator (fun _ => H (u n i)) s
    (∀ n, Integrable (G n) (volume.restrict (Ioc (0 : ℝ) (T : ℝ)))) ∧
    Integrable (fun s : ℝ => H s.toNNReal) (volume.restrict (Ioc (0 : ℝ) (T : ℝ))) ∧
    Tendsto (fun n => ∫ s in Ioc (0 : ℝ) (T : ℝ), |G n s - H s.toNNReal|)
      atTop (𝓝 0) := by
  intro u G
  let D : Set ℝ := Ioc (0 : ℝ) (T : ℝ)
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
  have hi (n : ℕ) : Integrable (G n) (volume.restrict D) :=
    (integrable_const C).mono' (hm n).aestronglyMeasurable
      ((ae_restrict_mem measurableSet_Ioc).mono (hbound n))
  have hmH : AEStronglyMeasurable (fun s : ℝ => H s.toNNReal) (volume.restrict D) :=
    aestronglyMeasurable_of_tendsto_ae atTop (fun n => (hm n).aestronglyMeasurable)
      ((ae_restrict_mem measurableSet_Ioc).mono hlim)
  have hiH : Integrable (fun s : ℝ => H s.toNNReal) (volume.restrict D) :=
    (integrable_const C).mono' hmH (Eventually.of_forall fun s => hb s.toNNReal)
  refine ⟨hi,hiH,?_⟩
  have h := tendsto_integral_of_dominated_convergence
    (μ := volume.restrict D) (F := fun n s => |G n s-H s.toNNReal|) (f := fun _ => 0)
    (fun _ => 2*C) (fun n => by simpa only [Real.norm_eq_abs,Pi.sub_apply] using ((hi n).sub hiH).norm.aestronglyMeasurable)
    (integrable_const (2*C))
    (fun n => (ae_restrict_mem measurableSet_Ioc).mono fun s hs => by
      rw [Real.norm_eq_abs,abs_abs]
      have hh : |G n s| ≤ C := hbound n s hs
      exact (abs_sub _ _).trans (by linarith [hh,hb s.toNNReal]))
    ((ae_restrict_mem measurableSet_Ioc).mono fun s hs => by
      simpa using ((hlim s hs).sub (tendsto_const_nhds (x := H s.toNNReal))).abs)
  simpa [D] using h
