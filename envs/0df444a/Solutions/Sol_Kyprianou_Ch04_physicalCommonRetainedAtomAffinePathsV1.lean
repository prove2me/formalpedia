-- Prove2me | solution 1 for Kyprianou.Ch04.physicalCommonRetainedAtomAffinePathsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T10:45:12.3165+00:00
-- url     : https://prove2.me/submissions/52008be5-be0d-4490-935f-9c7d41077190

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- A common retained atom set represents both physical cutoff paths. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal) (e b c : ℝ)
    (he : e < 1) (S : Finset NNReal) (j : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r)) :
    ∀ t : NNReal, t ≤ T →
      b * (t : ℝ) + (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ
        {x : ℝ | 1 ≤ |x|}, z.2 ∂ R) =
      b * (t : ℝ) + (∑ r ∈ S, if r ≤ t then (if 1 ≤ |j r| then j r else 0) else 0) ∧
      b * (t : ℝ) + (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ
        {x : ℝ | 1 ≤ |x|}, z.2 ∂ R) +
        (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ
          {x : ℝ | e < |x| ∧ |x| < 1}, z.2 ∂ R) - (t : ℝ)*c =
      (b-c) * (t : ℝ) + ∑ r ∈ S, if r ≤ t then j r else 0 := by
  intro t ht
  let D := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}
  let A := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  let B := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1}
  have hA : MeasurableSet A := measurableSet_Icc.prod
    (measurableSet_le measurable_const measurable_id.abs)
  have hB : MeasurableSet B := measurableSet_Icc.prod
    ((measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_lt measurable_id.abs measurable_const))
  have hAD : A ⊆ D := prod_mono (Icc_subset_Icc_right (by exact_mod_cast ht))
    (fun x hx => he.trans_le hx)
  have hBD : B ⊆ D := prod_mono (Icc_subset_Icc_right (by exact_mod_cast ht))
    (fun x hx => hx.1)
  have h1 := Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR A hA hAD Prod.snd
  have h2 := Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR B hB hBD Prod.snd
  have h1' : (∫ z in A, z.2 ∂ R) =
      ∑ r ∈ S, if r ≤ t then (if 1 ≤ |j r| then j r else 0) else 0 := by
    rw [h1]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [A,mem_prod,mem_Icc,mem_setOf_eq,r.coe_nonneg,true_and,NNReal.coe_le_coe]
    split_ifs <;> simp_all
  have h2' : (∫ z in B, z.2 ∂ R) =
      ∑ r ∈ S, if r ≤ t then (if |j r| < 1 then j r else 0) else 0 := by
    rw [h2]
    apply Finset.sum_congr rfl
    intro r hr
    simp only [B,mem_prod,mem_Icc,mem_setOf_eq,r.coe_nonneg,true_and,NNReal.coe_le_coe,
      (hS r hr).2.2,true_and]
    split_ifs <;> simp_all
  change b * (t : ℝ) + (∫ z in A, z.2 ∂ R) = _ ∧
    b * (t : ℝ) + (∫ z in A, z.2 ∂ R) + (∫ z in B, z.2 ∂ R) - _ = _
  rw [h1',h2']
  refine ⟨rfl,?_⟩
  have hsum : (∑ r ∈ S, if r ≤ t then (if 1 ≤ |j r| then j r else 0) else 0) +
      (∑ r ∈ S, if r ≤ t then (if |j r| < 1 then j r else 0) else 0) =
      ∑ r ∈ S, if r ≤ t then j r else 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    by_cases h : r ≤ t <;> by_cases h' : 1 ≤ |j r| <;> simp [h,h',not_lt.mpr,lt_of_not_ge]
  linarith
