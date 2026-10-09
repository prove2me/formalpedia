-- Prove2me | solution 1 for NestedSeatAlloc.IntPolicy.first_fare_positive_of_subdiff_condition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T17:00:21.593865+00:00
-- url     : https://prove2.me/submissions/0de94541-b132-4e63-854e-578ef17ae01e

import Mathlib
import Definitions.Def_NestedSeatAlloc_IntPolicy_Model
import Theorems.Thm_NestedSeatAlloc_IntPolicy_expRevenue_one_shift_mono_nonpos_fare

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory NestedSeatAlloc.IntPolicy

theorem solution {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (X : ℕ → Ω → ℝ) (f p : ℕ → ℝ)
    (hM : IsSeatModel P X f) (hp : IsProtectionPolicy p)
    (h20 : SubdiffCondition P X f p) :
    0 < f 1 := by
  by_contra hpositive
  have hf1le : f 1 ≤ 0 := le_of_not_gt hpositive
  have hp1 : 0 ≤ p 1 := hp 1 (by omega)
  have hshift : MonotoneOn
      (fun s => expRevenue P X f p 1 s - f 1 * s) (Set.Ici 0) :=
    expRevenue_one_shift_mono_nonpos_fare P X f p hM hp hf1le
  have hlocal : MonotoneOn
      (fun s => expRevenue P X f p 1 s - f 1 * s)
      (Set.Ici (p 1)) := by
    intro s hs t ht hst
    exact hshift (le_trans hp1 hs) (le_trans hp1 ht) hst
  have hacc : AccPt (p 1) (Filter.principal (Set.Ici (p 1))) := by
    apply accPt_iff_frequently.mpr
    exact (frequently_gt_nhds (p 1)).mono
      (fun z hz => ⟨ne_of_gt hz, le_of_lt hz⟩)
  obtain ⟨r, hder, hrle⟩ := (h20 1 (by omega)).1
  have hlin : HasDerivWithinAt (fun s : ℝ => f 1 * s)
      (f 1) (Set.Ici (p 1)) (p 1) := by
    simpa only [id_eq, mul_one] using
      ((hasDerivAt_id (p 1)).const_mul (f 1)).hasDerivWithinAt
  have hshder : HasDerivWithinAt
      (fun s => expRevenue P X f p 1 s - f 1 * s)
      (r - f 1) (Set.Ici (p 1)) (p 1) :=
    hder.sub hlin
  have hnonneg : 0 ≤ r - f 1 :=
    HasDerivWithinAt.nonneg_of_monotoneOn hacc hshder hlocal
  have hfare : f 2 < f 1 := hM.fare_strictAnti 1 (by omega)
  linarith
