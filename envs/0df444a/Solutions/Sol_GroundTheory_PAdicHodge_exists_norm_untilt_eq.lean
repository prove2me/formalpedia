-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_norm_untilt_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:32:18.581834+00:00
-- url     : https://prove2.me/submissions/4de6bb24-7cc5-4419-9094-f0d4dbeb4f5d

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
theorem _root_.solution (a : normInteger K) (ha : ‖(p : K)‖ < ‖(a : K)‖) :
    ∃ x : PreTilt (normInteger K) p, ‖((x.untilt : normInteger K) : K)‖ = ‖(a : K)‖ := by
  obtain ⟨x, hx⟩ := exists_mk_untilt_eq (p := p) a
  rw [mk_eq_mk_iff_norm_sub_le] at hx
  refine ⟨x, ?_⟩
  have hne : ‖(a : K)‖ ≠ ‖((x.untilt : normInteger K) : K) - a‖ := (hx.trans_lt ha).ne'
  have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne
  rw [add_sub_cancel] at this
  rw [this, max_eq_left (hx.trans ha.le)]
end GroundTheory.PAdicHodge
