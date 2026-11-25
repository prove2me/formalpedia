-- Prove2me | solution 1 for GroundTheory.PAdicHodge.exists_sub_far_of_isClosed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:18:13.431415+00:00
-- url     : https://prove2.me/submissions/9a195f01-c745-4dbc-9aad-6f4ba5486659

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_OrthoBasis

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
variable {k E : Type*} [NontriviallyNormedField k] [IsUltrametricDist k]
  [NormedAddCommGroup E] [NormedSpace k E] [IsUltrametricDist E]
omit [IsUltrametricDist k] [IsUltrametricDist E]
namespace GroundTheory.PAdicHodge
theorem _root_.solution {U : Submodule k E} (hU : IsClosed (U : Set E)) {x : E}
    (hx : x ∉ U) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ u ∈ U, ∀ u' ∈ U, s * ‖x - u‖ ≤ ‖x - u - u'‖ := by
  have hne : (U : Set E).Nonempty := ⟨0, U.zero_mem⟩
  have hd : 0 < Metric.infDist x U := (hU.notMem_iff_infDist_pos hne).1 hx
  have hlt : Metric.infDist x U < Metric.infDist x U / s := by
    rw [lt_div_iff₀ hs0]; nlinarith
  obtain ⟨u, huU, hu⟩ := (Metric.infDist_lt_iff hne).1 hlt
  refine ⟨u, huU, fun u' hu' => ?_⟩
  have h1 : Metric.infDist x U ≤ dist x (u + u') :=
    Metric.infDist_le_dist_of_mem (U.add_mem huU hu')
  rw [dist_eq_norm, ← sub_sub] at h1
  rw [dist_eq_norm] at hu
  have h2 := (lt_div_iff₀ hs0).1 hu
  nlinarith
end GroundTheory.PAdicHodge
