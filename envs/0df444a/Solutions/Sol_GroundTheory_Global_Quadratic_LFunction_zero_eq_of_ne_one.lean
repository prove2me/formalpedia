-- Prove2me | solution 1 for GroundTheory.Global.Quadratic.LFunction_zero_eq_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:46:36.19986+00:00
-- url     : https://prove2.me/submissions/21973855-5f77-49a4-9060-c02f54187a47

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_AnalyticClassNumber_QuadraticHurwitzZero
import Theorems.Thm_GroundTheory_Global_Quadratic_LFunction_zero_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open Complex HurwitzZeta Filter Topology Set
open GroundTheory GroundTheory.Global GroundTheory.Global.Quadratic
namespace GroundTheory.Global.Quadratic
theorem _root_.solution {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    DirichletCharacter.LFunction χ 0 = -(1 / N) * ∑ a : ZMod N, χ a * (a.val : ℂ) := by
  rcases eq_or_ne N 1 with rfl | hN1
  · exact absurd (MulChar.ext fun u ↦ by rw [Subsingleton.elim u 1, Units.val_one, map_one,
      map_one]) hχ
  have : Nontrivial (ZMod N) := ZMod.nontrivial_iff.2 hN1
  exact LFunction_zero_eq (MulChar.map_nonunit χ not_isUnit_zero) (MulChar.sum_eq_zero_of_ne_one hχ)
end GroundTheory.Global.Quadratic
