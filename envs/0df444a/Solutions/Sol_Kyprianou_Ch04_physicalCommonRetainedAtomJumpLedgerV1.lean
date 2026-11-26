-- Prove2me | solution 1 for Kyprianou.Ch04.physicalCommonRetainedAtomJumpLedgerV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:13:40.211817+00:00
-- url     : https://prove2.me/submissions/ecfc3d92-b77b-4522-9036-db2d425404f3

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_finitePhysicalAtomsSubwindowIntegralV1
open MeasureTheory Filter Set
open scoped NNReal ENNReal Classical
set_option autoImplicit false

/-- The full nonlinear jump sum splits into its remainder and the two weighted mark integrals. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal) (e : ℝ)
    (he : e < 1) (S : Finset NNReal) (j : NNReal → ℝ)
    (hS : ∀ r ∈ S, 0 < r ∧ r ≤ T ∧ e < |j r|)
    (hR : R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}) =
      ∑ r ∈ S, Measure.dirac ((r : ℝ),j r))
    (Y L : NNReal → ℝ) (f fx : ℝ → ℝ → ℝ)
    (hJ : ∀ r ∈ S, Y r = L r + j r) :
    (∑ r ∈ S, (f r (Y r) - f r (L r))) =
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|},
        (f z.1 (L z.1.toNNReal + z.2) - f z.1 (L z.1.toNNReal) -
          z.2 * fx z.1 (L z.1.toNNReal)) ∂ R) +
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|},
        z.2 * fx z.1 (L z.1.toNNReal) ∂ R) +
      (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1},
        z.2 * fx z.1 (L z.1.toNNReal) ∂ R) := by
  let D := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x|}
  let A := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | 1 ≤ |x|}
  let B := Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e < |x| ∧ |x| < 1}
  have hD : MeasurableSet D := measurableSet_Icc.prod
    (measurableSet_lt measurable_const measurable_id.abs)
  have hA : MeasurableSet A := measurableSet_Icc.prod
    (measurableSet_le measurable_const measurable_id.abs)
  have hB : MeasurableSet B := measurableSet_Icc.prod
    ((measurableSet_lt measurable_const measurable_id.abs).inter
      (measurableSet_lt measurable_id.abs measurable_const))
  have hAD : A ⊆ D := prod_mono subset_rfl (fun x hx => he.trans_le hx)
  have hBD : B ⊆ D := prod_mono subset_rfl (fun x hx => hx.1)
  change _ = (∫ z in D, _ ∂ R) + (∫ z in A, _ ∂ R) + (∫ z in B, _ ∂ R)
  rw [Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR D hD subset_rfl,
    Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR A hA hAD,
    Kyprianou.Ch04.finitePhysicalAtomsSubwindowIntegralV1 R D S j hR B hB hBD,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  have h := hS r hr
  simp only [D,A,B,mem_prod,mem_Icc,mem_setOf_eq,r.coe_nonneg,true_and,
    NNReal.coe_le_coe,h.2.1,h.2.2,Real.toNNReal_coe,hJ r hr]
  by_cases hh : 1 ≤ |j r|
  · simp [hh,not_lt.mpr hh]
  · simp [hh,lt_of_not_ge hh]
