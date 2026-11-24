-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.part_exercise8_11_i_v2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T12:55:29.871251+00:00
-- url     : https://prove2.me/submissions/952969bd-730b-4605-adf6-7ece0579b15b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_Kyprianou_Ch08_StageB_source_result8_1_v2
import Theorems.Thm_Kyprianou_Ch08_StageB_p2m810_inf_exit_ratio
import Theorems.Thm_Kyprianou_Ch08_StageB_source_zscale_ge_one
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
theorem solution : exercise8_11_i := by
  intro Ω mΩ P hP D q x a hq ha hx hxa
  obtain ⟨ψ, W, hψ, hW, _, _, _, hExit⟩ := source_result8_1_v2 Ω P D
  obtain ⟨hw, hu, hd⟩ := hExit q x a hq ha hxa
  have hZ : Zscale q (W q) a ≠ 0 := by
    have h := source_zscale_ge_one ψ W hW q a hq ha.le
    linarith
  rw [p2m810_inf_exit_ratio Ω P D ψ W hψ hW q x a hq ha hx.le hxa,
    p2m810_inf_exit_ratio Ω P D ψ W hψ hW q 0 a hq ha le_rfl ha.le, hu, hd]
  rw [show Zscale q (W q) 0 = 1 by simp [Zscale, integratedScale]]
  field_simp [hw.ne', hZ] <;> ring
