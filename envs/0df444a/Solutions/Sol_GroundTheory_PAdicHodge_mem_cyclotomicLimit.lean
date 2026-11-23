-- Prove2me | solution 1 for GroundTheory.PAdicHodge.mem_cyclotomicLimit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:50:13.264821+00:00
-- url     : https://prove2.me/submissions/d636153b-5b79-4da8-a657-85a2706843a7

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Theorems.Thm_GroundTheory_PAdicHodge_cyclotomicLayer_mono

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.PAdicHodge
open IntermediateField Polynomial Module
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
namespace GroundTheory.PAdicHodge
theorem _root_.solution {x : PadicAlgCl p} :
    x ∈ cyclotomicLimit K ↔ ∃ n, x ∈ cyclotomicLayer K n := by
  rw [← SetLike.mem_coe, cyclotomicLimit,
    coe_iSup_of_directed (cyclotomicLayer_mono K).directed_le, Set.mem_iUnion]
  rfl
end GroundTheory.PAdicHodge
