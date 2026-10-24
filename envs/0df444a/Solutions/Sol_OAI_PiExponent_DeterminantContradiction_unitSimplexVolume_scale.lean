-- Prove2me | solution 1 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_scale
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-24T02:10:58.057855+00:00
-- url     : https://prove2.me/submissions/1e0f629c-5c9d-4127-8e87-6eebe1a52541

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

end PXSc

theorem solution
    (n : Nat) (c : Real) (hc : 0 ≤ c) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} =
      ENNReal.ofReal (c ^ n) *
        MeasureTheory.volume
          {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
            (Finset.univ.sum fun i : Fin n => x i) ≤ 1} := by
  have := PXSc.S_eq_smul n c hc
  unfold PXSc.S at this
  rw [this]
  exact PXSc.vol_smul n c hc
