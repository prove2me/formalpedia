-- Prove2me | solution 1 for GlobalTheory.ArchChar.tendsto_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:47.06481+00:00
-- url     : https://prove2.me/submissions/e5ee87f5-f10a-4181-83b0-3d861a42fa90

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousCharUnitsComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.ArchChar
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.ArchChar
theorem _root_.solution : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop := by
  exact tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
end GlobalTheory.ArchChar
