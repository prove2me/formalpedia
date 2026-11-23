-- Prove2me | solution 1 for GlobalTheory.map_zero_of_isBigO_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:04:20.320041+00:00
-- url     : https://prove2.me/submissions/0a286473-fde4-467e-9dab-910c1e57a34e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]
namespace GlobalTheory
theorem _root_.solution {f : E → F} {L : E →L[ℂ] F}
    (h : (fun x => f x - L x) =O[𝓝 0] fun x => ‖x‖ ^ 2) : f 0 = 0 := by
  obtain ⟨C, hC⟩ := h.bound
  simpa using hC.self_of_nhds
end GlobalTheory
