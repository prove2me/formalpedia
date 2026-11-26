-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45RetainedWeightedLedgerV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T18:54:03.816305+00:00
-- url     : https://prove2.me/submissions/a9b18d5b-5bee-419a-a5c0-6888d943bb90

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false
/-- Evaluate the fixed-cutoff weighted jump and compensation ledger. -/
theorem solution (R : Measure (ℝ × ℝ)) (ν : Measure ℝ) (T : NNReal) (e b : ℝ)
    (he : e < 1) (S : Finset NNReal) (j : NNReal → ℝ)
    (hs : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (H : ℝ → ℝ) (t : NNReal) (ht : t ≤ T) :
    let c := ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ ν
    b * (∫ s in Icc (0 : ℝ) (t : ℝ), H s) +
      (∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}, z.2 * H z.1 ∂ R) +
      ((∫ z in Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
        z.2 * H z.1 ∂ R) - ∫ s in Icc (0 : ℝ) (t : ℝ),
          ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x * H s ∂ ν) =
    (b-c) * (∫ s in Icc (0 : ℝ) (t : ℝ), H s) +
      ∑ r ∈ S, if r ≤ t then j r * H (r : ℝ) else 0 := by
  dsimp only
  let c := ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x ∂ ν
  let D := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}
  let B := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  let A := Icc (0 : ℝ) (t : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1}
  let g := fun z : ℝ × ℝ => z.2 * H z.1
  have hB : MeasurableSet B := measurableSet_Icc.prod
    (measurableSet_le measurable_const measurable_id.abs)
  have hA : MeasurableSet A := measurableSet_Icc.prod
    ((measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_lt measurable_id.abs measurable_const))
  have hBD : B ⊆ D := prod_mono (Icc_subset_Icc_right (by exact_mod_cast ht))
    (fun x hx => he.trans_le hx)
  have hAD : A ⊆ D := prod_mono (Icc_subset_Icc_right (by exact_mod_cast ht))
    (fun x hx => hx.1)
  have hI : (∫ z in B, g z ∂ R) + (∫ z in A, g z ∂ R) =
      ∑ r ∈ S, if r ≤ t then j r * H (r : ℝ) else 0 := by
    rw [Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR B hB hBD,
      Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR A hA hAD,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have hret := (hs r hr).2.2
    simp only [B,A,mem_prod,mem_Icc,mem_setOf_eq,r.coe_nonneg,true_and,
      NNReal.coe_le_coe,g,hret]
    by_cases hrt : r ≤ t
    · by_cases hbig : 1 ≤ |j r|
      · simp [hrt,hbig,not_lt.mpr hbig]
      · simp [hrt,hbig,lt_of_not_ge hbig]
    · simp [hrt]
  have hc : (∫ s in Icc (0 : ℝ) (t : ℝ),
      ∫ x in {x : ℝ | e < |x| ∧ |x| < 1}, x * H s ∂ ν) =
      c * (∫ s in Icc (0 : ℝ) (t : ℝ), H s) := by
    simp_rw [integral_mul_const]
    exact integral_const_mul _ _
  rw [hc,← hI]
  dsimp only [c,A,B,g]
  ring
