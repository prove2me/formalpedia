-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.simplex_volume_succ_ENNReal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:15:57.820846+00:00
-- url     : https://prove2.me/submissions/c68bf372-8834-4d2f-9609-9a9d0656ff94

import Mathlib

open MeasureTheory
open scoped BigOperators Pointwise

namespace PXSc

def S (n : ℕ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (Finset.univ.sum fun i : Fin n => x i) ≤ c}

lemma image_eq (n : ℕ) (a : ℝ) :
    (fun y : Fin n → ℝ => fun i => a * y i) '' S n 1 = a • S n 1 := by
  rw [← Set.image_smul]; rfl

lemma S_eq_smul (n : ℕ) (c : ℝ) (hc : 0 ≤ c) : S n c = c • S n 1 := by
  ext x
  constructor
  · rintro ⟨h0, hs⟩
    rcases hc.eq_or_lt with rfl | hc'
    · refine ⟨0, ⟨fun i => le_rfl, by simp⟩, ?_⟩
      have hx : ∀ i, x i = 0 := by
        intro i
        have hle : x i ≤ ∑ j, x j :=
          Finset.single_le_sum (fun j _ => h0 j) (Finset.mem_univ i)
        exact le_antisymm (hle.trans hs) (h0 i)
      funext i; simp [hx i]
    · refine ⟨c⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hc) (h0 i)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ hc']; simpa using hs
      · simp [smul_smul, hc'.ne']
  · rintro ⟨y, ⟨h0, hs⟩, rfl⟩
    refine ⟨fun i => ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg hc (h0 i)
    · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
      simpa using mul_le_mul_of_nonneg_left hs hc

lemma vol_smul (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    volume (a • S n 1) = ENNReal.ofReal (a ^ n) * volume (S n 1) := by
  rw [Measure.addHaar_smul, Module.finrank_fin_fun, abs_of_nonneg (pow_nonneg ha n)]


lemma S_meas (n : ℕ) (c : ℝ) : MeasurableSet (S n c) := by
  unfold S
  rw [Set.setOf_and]
  refine MeasurableSet.inter ?_ ?_
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_le measurable_const (measurable_pi_apply i))
  · exact measurableSet_le (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)) measurable_const

lemma S_neg (n : ℕ) (c : ℝ) (hc : c < 0) : S n c = ∅ := by
  ext x
  simp only [S, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
  intro h0
  exact lt_of_lt_of_le hc (Finset.sum_nonneg (fun i _ => h0 i))

lemma vol_S (n : ℕ) (c : ℝ) (hc : 0 ≤ c) :
    volume (S n c) = ENNReal.ofReal (c ^ n) * volume (S n 1) := by
  rw [S_eq_smul n c hc]; exact vol_smul n c hc

end PXSc

namespace PXSl

lemma slice (m : ℕ) (s : Set (Fin (m + 1) → ℝ)) (hs : MeasurableSet s) :
    volume s = ∫⁻ t, volume {y : Fin m → ℝ | Fin.cons t y ∈ s} := by
  have hp := (volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm
  have hs' : MeasurableSet ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm ⁻¹' s) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0).symm.measurable hs
  rw [← hp.measure_preimage hs.nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_apply hs']
  refine lintegral_congr (fun t => ?_)
  congr 1
  ext y
  simp [MeasurableEquiv.piFinSuccAbove, Fin.insertNthEquiv, Fin.insertNth_zero']

end PXSl

namespace PXSV
open PXSc

lemma slice_S (n : ℕ) (t : ℝ) :
    {y : Fin n → ℝ | Fin.cons t y ∈ S (n + 1) 1} =
      (if t ∈ Set.Icc (0:ℝ) 1 then S n (1 - t) else ∅) := by
  ext y
  simp only [S, Set.mem_setOf_eq, Fin.forall_fin_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.sum_univ_succ]
  by_cases ht : t ∈ Set.Icc (0:ℝ) 1
  · rw [if_pos ht]
    simp only [S, Set.mem_setOf_eq]
    constructor
    · rintro ⟨⟨_, h1⟩, h2⟩; exact ⟨h1, by linarith⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨ht.1, h1⟩, by linarith⟩
  · rw [if_neg ht]
    simp only [Set.mem_empty_iff_false, iff_false, not_and, not_le]
    rintro ⟨h0, h1⟩
    have hs : 0 ≤ ∑ i, y i := Finset.sum_nonneg (fun i _ => h1 i)
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at ht
    rcases ht with ht | ht
    · exact absurd h0 (not_le.2 ht)
    · linarith

lemma integral_pow (n : ℕ) :
    ∫⁻ t in Set.Icc (0:ℝ) 1, ENNReal.ofReal ((1 - t) ^ n) = ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal]
  · congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one]
    rw [intervalIntegral.integral_comp_sub_left (fun x => x ^ n)]
    simp [integral_pow]
  · exact (continuous_const.sub continuous_id |>.pow n).integrableOn_Icc
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact pow_nonneg (by linarith [ht.2]) n

theorem succ (n : ℕ) :
    volume (S (n + 1) 1) = ENNReal.ofReal (1 / ((n + 1 : ℕ) : ℝ)) * volume (S n 1) := by
  rw [PXSl.slice n _ (S_meas _ _)]
  simp_rw [slice_S]
  have : ∀ t, volume (if t ∈ Set.Icc (0:ℝ) 1 then S n (1 - t) else ∅)
      = Set.indicator (Set.Icc (0:ℝ) 1) (fun t => ENNReal.ofReal ((1 - t) ^ n) * volume (S n 1)) t := by
    intro t
    by_cases ht : t ∈ Set.Icc (0:ℝ) 1
    · rw [if_pos ht, Set.indicator_of_mem ht, vol_S n _ (by linarith [ht.2])]
    · rw [if_neg ht, Set.indicator_of_notMem ht]; simp
  simp_rw [this]
  rw [lintegral_indicator measurableSet_Icc, lintegral_mul_const _ (by fun_prop), integral_pow]

end PXSV

theorem solution (n : Nat) :
    MeasureTheory.volume
      {x : Fin (n + 1) → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin (n + 1) => x i) ≤ 1} =
      ENNReal.ofReal (1 / ((n + 1 : Nat) : Real)) *
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1} :=
  PXSV.succ n
