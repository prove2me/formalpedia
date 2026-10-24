-- Prove2me | solution 2 for OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_cutoff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-23T20:06:16.422073+00:00
-- url     : https://prove2.me/submissions/af614f25-830c-4ce7-bb7e-d57a79136d8c

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib
import Theorems.Thm_OAI_PiExponent_DeterminantContradiction_unitSimplexVolume_factorial_aux

open MeasureTheory

section
open MeasureTheory Filter Topology
theorem O3dil (n : Nat) (c : Real) (hc : 0 ≤ c) :
    {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i : Fin n, x i) ≤ c} =
      (fun x : Fin n → Real => c • x) ''
        {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧ (∑ i : Fin n, x i) ≤ 1} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨hx, hs⟩
    rcases hc.lt_or_eq with hc | hc
    · refine ⟨c⁻¹ • x, ⟨fun i => ?_, ?_⟩, ?_⟩
      · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_nonneg (inv_nonneg.2 hc.le) (hx i)
      · simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
        rw [inv_mul_le_iff₀ hc]; linarith
      · simp [smul_smul, hc.ne']
    · subst hc
      refine ⟨0, ⟨fun i => le_refl _, by simp⟩, ?_⟩
      have h0 : ∀ i ∈ Finset.univ, x i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hx i)).1
          (le_antisymm hs (Finset.sum_nonneg fun i _ => hx i))
      ext i; simp [h0 i (Finset.mem_univ _)]
  · rintro ⟨y, ⟨hy, hs⟩, rfl⟩
    refine ⟨fun i => mul_nonneg hc (hy i), ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, ← Finset.mul_sum]
    nlinarith

theorem O3cutoff (n : Nat) (c : Real) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} =
      (if 0 ≤ c then ENNReal.ofReal (c ^ n / (Nat.factorial n : Real)) else 0) := by
  split_ifs with hc
  · rw [O3dil n c hc, Set.image_smul, Measure.addHaar_smul,
      OAI.PiExponent.DeterminantContradiction.unitSimplexVolume_factorial_aux,
      ← ENNReal.ofReal_mul (by positivity), Module.finrank_fin_fun, abs_of_nonneg (pow_nonneg hc n)]
    congr 1; ring
  · push_neg at hc
    have : {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro hx
      exact lt_of_lt_of_le hc (Finset.sum_nonneg fun i _ => hx i)
    simp [this]

end

open MeasureTheory Filter Topology in

theorem solution (n : Nat) (c : Real) :
    MeasureTheory.volume
      {x : Fin n → Real | (∀ i, 0 ≤ x i) ∧
        (Finset.univ.sum fun i : Fin n => x i) ≤ c} =
      (if 0 ≤ c then ENNReal.ofReal (c ^ n / (Nat.factorial n : Real)) else 0) := by
  exact O3cutoff n c
