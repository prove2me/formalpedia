-- Prove2me | solution 1 for GreedWorks.OnlineTime.eq_13
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T14:25:52.967834+00:00
-- url     : https://prove2.me/submissions/dba42e42-20c8-4c23-9264-9638321088ab

import Mathlib
import Definitions.Def_GreedWorks_OnlineTime_Model
import Definitions.Def_GreedWorks_OnlineTime_TimeIndexedLP
import Theorems.Thm_GreedWorks_OnlineTime_eq_13_relaxation

open MeasureTheory GreedWorks.OnlineTime

theorem solution {M : Type*} [Fintype M] [Nonempty M] {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (I : StochasticInstance M n Ω) :
    (∀ y, IsFeasibleS I.eligible I.release (mean I) (cvSquared I) y →
      ∃ y', IsFeasibleP I.eligible I.release (mean I) y' ∧
        valueP I.eligible (mean I) I.weight y' ≤
          (1 + I.Delta / 2) * valueS I.eligible (mean I) (cvSquared I) I.weight y) ∧
    (∀ pol : GreedWorks.OnlineList.Policy M n, IsAdmissible I pol →
      ∃ y, IsFeasibleS I.eligible I.release (mean I) (cvSquared I) y ∧
        valueS I.eligible (mean I) (cvSquared I) I.weight y ≤ policyCost I pol) := by
  classical
  refine ⟨fun y hy => ⟨y, hy.1, ?_⟩, eq_13_relaxation I⟩
  obtain ⟨hP, h5⟩ := hy
  obtain ⟨hy0, hyE, hyR, hyS, hyS2, hy1, hy3⟩ := hP
  unfold valueP valueS
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j _ => ?_)
  have key : completionP I.eligible (mean I) y j ≤
      (1 + I.Delta / 2) * completionS I.eligible (mean I) (cvSquared I) y j := by
    have hterm : ∀ i ∈ Finset.univ.filter (fun i => I.eligible i j),
        ∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) + y i j s / 2) ≤
        ∑' s : ℕ, (y i j s / mean I i j * ((s : ℝ) + 1 / 2) +
          (1 - cvSquared I i j) / 2 * y i j s) + I.Delta / 2 * ∑' s : ℕ, y i j s := by
      intro i hi
      have hel : I.eligible i j := (Finset.mem_filter.mp hi).2
      have hcv : cvSquared I i j ≤ I.Delta := by
        have hmean : 1 ≤ mean I i j := I.meanAtLeastOne i j hel
        unfold cvSquared
        rw [div_le_iff₀ (by positivity)]
        exact I.cvBound i j hel
      have hA : Summable (fun s : ℕ => y i j s / mean I i j * ((s : ℝ) + 1 / 2)) :=
        ((hyS2 i j).mul_left (mean I i j)⁻¹).congr (fun s => by ring)
      have hB : Summable (fun s : ℕ => y i j s / mean I i j * ((s : ℝ) + 1 / 2) +
          (1 - cvSquared I i j) / 2 * y i j s) := hA.add ((hyS i j).mul_left _)
      rw [← tsum_mul_left, ← hB.tsum_add ((hyS i j).mul_left _)]
      refine (hA.add ((hyS i j).div_const 2)).tsum_le_tsum (fun s => ?_)
        (hB.add ((hyS i j).mul_left _))
      have h0 := hy0 i j s
      have := mul_le_mul_of_nonneg_right hcv h0
      linarith
    have hsum := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    have h5j := h5 j
    have hΔ := I.Delta_nonneg
    unfold completionP
    have hC0 : 0 ≤ ∑ i ∈ Finset.univ.filter (fun i => I.eligible i j), ∑' s : ℕ, y i j s :=
      Finset.sum_nonneg (fun i _ => tsum_nonneg (fun s => hy0 i j s))
    unfold completionS at h5j ⊢
    nlinarith
  have hw := I.weight_nonneg j
  calc I.weight j * completionP I.eligible (mean I) y j
      ≤ I.weight j * ((1 + I.Delta / 2) * completionS I.eligible (mean I) (cvSquared I) y j) :=
        mul_le_mul_of_nonneg_left key hw
    _ = _ := by ring
