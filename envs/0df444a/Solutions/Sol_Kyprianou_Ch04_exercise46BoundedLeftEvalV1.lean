-- Prove2me | solution 1 for Kyprianou.Ch04.exercise46BoundedLeftEvalV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:23:10.737827+00:00
-- url     : https://prove2.me/submissions/6f12802f-dce0-46d9-a636-bf7134aba3f0

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise46LeftLimitMeshConvergenceV1
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_prejump_fractional_left_time_mesh
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
set_option autoImplicit false
theorem solution
    {Omega : Type} [m : MeasurableSpace Omega]
    (P : Measure Omega) (G : Filtration NNReal m)
    (L : SpectrallyNegativeLevy P G)
    (a : Omega → NNReal) (T : NNReal) (hT : ∀ w, a w ≤ T)
    (ha : Measurable[G.rightCont T] a)
    (hJoint : @Measurable (NNReal × Omega) Real
      (@Prod.instMeasurableSpace NNReal Omega inferInstance (G.rightCont T))
      inferInstance (fun z => L.X (min z.1 T) z.2)) :
    Measurable[G.rightCont T] (fun w =>
      Function.leftLim (fun u : NNReal => L.X u w) (a w)) := by
  let c : Nat → NNReal → NNReal := fun n t => t - t * (1 / 2 : NNReal) ^ (n + 1)
  let V : Nat → Omega → Real := fun n w => L.X (min (c n (a w)) T) w
  have hm := avram_wave4_04b_prejump_fractional_left_time_mesh
  have hid : @Measurable Omega Omega (G.rightCont T) (G.rightCont T) id :=
    @measurable_id Omega (G.rightCont T)
  have hV (n : Nat) : Measurable[G.rightCont T] (V n) :=
    hJoint.comp (((hm.1 n).comp ha).prodMk hid)
  refine @measurable_of_tendsto_metrizable Omega Real (G.rightCont T)
    _ _ _ _ V _ hV ?_
  rw [tendsto_pi_nhds]
  intro w
  have he (n : Nat) : min (c n (a w)) T = c n (a w) :=
    min_eq_left ((tsub_le_self).trans (hT w))
  simpa only [V, he, c] using
    (Kyprianou.Ch04.exercise46LeftLimitMeshConvergenceV1
      (fun u => L.X u w) (L.leftLim w) (a w))
