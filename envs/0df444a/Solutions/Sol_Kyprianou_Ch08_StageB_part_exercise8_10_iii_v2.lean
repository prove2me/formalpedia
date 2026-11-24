-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.part_exercise8_10_iii_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T21:48:41.417515+00:00
-- url     : https://prove2.me/submissions/e4ef2207-6f0b-412c-b70c-4b827125c762
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_part_exercise8_10_ii_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_last_exit_restart_kernel
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_restart_kernel_pointwise_exponential
open MeasureTheory ProbabilityTheory Set Filter Topology
open Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution : exercise8_10_iii := by
  intro Ω mΩ P hP D ψ W hψ hW hDrift
  obtain ⟨d,hd,hminus,_,_⟩ :=
    part_exercise8_10_ii_v2 Ω P D ψ W hψ hW hDrift
  refine ⟨d,hd,?_⟩
  intro q y hq hy
  rw [p2m810_last_exit_restart_kernel Ω P D q y hq hy hDrift,
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [D.levy.cadlag_ae] with ω hc
  exact p2m810_restart_kernel_pointwise_exponential Ω P D.X ω q y
    (Phi ψ q) (d * deriv (Phi ψ) q) (fun t => (hc t).1)
    (fun x hx => hminus q x hq hx)
