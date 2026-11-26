-- Prove2me | solution 1 for Kyprianou.Ch04.stoppingTimeMinMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:20:51.5196+00:00
-- url     : https://prove2.me/submissions/9a1c7ba8-0eee-4554-a629-657d8dc4e13e

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- A stopping time clipped at a deterministic clock is measurable at that clock. -/
theorem solution {Omega : Type} [MeasurableSpace Omega]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (tau : Omega → WithTop NNReal) (htau : IsStoppingTime F tau) (t : NNReal) :
    Measurable[F t] (fun w => min (tau w) (t : WithTop NNReal)) := by
  apply measurable_of_Iic
  intro a
  induction a using WithTop.recTopCoe with
  | top =>
    convert MeasurableSet.univ (m := F t) using 1
    ext w
    simp
  | coe r =>
    by_cases hr : t ≤ r
    · have he : (fun w => min (tau w) (t : WithTop NNReal)) ⁻¹' Iic (r : WithTop NNReal) =
          Set.univ := by
        ext w
        simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_univ,iff_true]
        exact (min_le_right _ _).trans (WithTop.coe_le_coe.mpr hr)
      rw [he]
      exact MeasurableSet.univ
    · have hrt : r ≤ t := (lt_of_not_ge hr).le
      have he : (fun w => min (tau w) (t : WithTop NNReal)) ⁻¹' Iic (r : WithTop NNReal) =
          {w | tau w ≤ (r : WithTop NNReal)} := by
        ext w
        simp only [Set.mem_preimage,Set.mem_Iic,Set.mem_setOf_eq,min_le_iff,
          WithTop.coe_le_coe,hr,or_false]
      rw [he]
      exact F.mono hrt _ (htau r)
