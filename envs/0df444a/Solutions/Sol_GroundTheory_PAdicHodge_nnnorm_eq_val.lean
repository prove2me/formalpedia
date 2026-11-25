-- Prove2me | solution 1 for GroundTheory.PAdicHodge.nnnorm_eq_val
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:58.964364+00:00
-- url     : https://prove2.me/submissions/3d52cd5b-84be-4c43-83c6-5b843687337f

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_PerfectoidField
import Definitions.Def_GroundTheory_PAdicHodge_TiltValuation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.PAdicHodge
open Filter Topology NNReal
variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [Fact p.Prime] [IsPerfectoidField K p]
namespace GroundTheory.PAdicHodge
theorem _root_.solution (x : PreTilt (normInteger K) p) :
    ‖x‖₊ = PreTilt.val K NormedField.valuation (normInteger K) normInteger_integers p x := by
  rw [val_eq_nnnorm_untilt]; rfl
end GroundTheory.PAdicHodge
