-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.integrableOn_reflect_Ioc_of_halfline
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T07:13:09.792514+00:00
-- url     : https://prove2.me/submissions/279cef8c-a7ae-47a2-b216-46634c800dde

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_B
set_option autoImplicit false

open MeasureTheory Set

theorem solution (f : ℝ → ℝ) (x : ℝ) (hx : 0 ≤ x)
    (hf : IntegrableOn f (Set.Ioi (0 : ℝ)) volume) :
    IntegrableOn (fun s : ℝ => f (x - s)) (Set.Ioc (0 : ℝ) x) volume := by
  have hsubset : Set.Ioc (0 : ℝ) x ⊆ Set.Ioi (0 : ℝ) := by
    intro s hs
    exact hs.1
  have hlocal : IntervalIntegrable f volume 0 x :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).2 (hf.mono_set hsubset)
  have href : IntervalIntegrable (fun s : ℝ => f (x - s)) volume x 0 := by
    simpa using hlocal.comp_sub_left x
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hx).1 href.symm
