-- Prove2me | solution 1 for GlobalTheory.ArchChar.abs_coord_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:45.688497+00:00
-- url     : https://prove2.me/submissions/6d07dc8d-4b05-4922-8fbc-8a7b0927d56f

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
theorem _root_.solution {a y : ι → ℝ} {C : ℝ} (h : ‖a - y‖ ≤ C) (i : ι) : |a i - y i| ≤ C := by
  have := norm_le_pi_norm (a - y) i
  rw [Pi.sub_apply, Real.norm_eq_abs] at this
  linarith
end GlobalTheory.ArchChar
