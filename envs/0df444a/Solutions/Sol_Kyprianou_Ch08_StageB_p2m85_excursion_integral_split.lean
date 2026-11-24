-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.p2m85_excursion_integral_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T18:46:00.409572+00:00
-- url     : https://prove2.me/submissions/5e899249-df2b-4ba0-aba7-b9344094706b

import Mathlib
import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal
open Kyprianou.Ch08 Kyprianou.Ch08.StageB ProbabilityTheory

theorem solution
    (ψ : ℝ → ℝ) (V : ℝ → ℝ) (n : Measure ℝ)
    (hr : HasQExcursionScaleRepresentation ψ 0 V n)
    (u v : ℝ) (hu : 0 < u) (hv : u < v) :
    (∫ t in u..v, Phi ψ 0 + (n (Ici t)).toReal) =
      (v-u)*Phi ψ 0 + ∫ t in u..v, (n (Ici t)).toReal := by
  have hi : IntervalIntegrable (fun t => Phi ψ 0 + (n (Ici t)).toReal) volume u v := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hv.le]
    exact (hr.2 u v hu hv).1
  have hj := hi.sub (intervalIntegrable_const (c := Phi ψ 0))
  have hk : IntervalIntegrable (fun t => (n (Ici t)).toReal) volume u v := by
    simpa only [add_sub_cancel_left] using hj
  rw [intervalIntegral.integral_add intervalIntegrable_const hk]
  simp
