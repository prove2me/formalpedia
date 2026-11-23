-- Prove2me | solution 1 for GlobalTheory.hasFDerivAt_of_isBigO_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:37:46.518871+00:00
-- url     : https://prove2.me/submissions/2ada7658-e88b-4ddc-b126-6192a139e3ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Theorems.Thm_GlobalTheory_map_zero_of_isBigO_sq

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
    (h : (fun x => f x - L x) =O[𝓝 0] fun x => ‖x‖ ^ 2) : HasFDerivAt f L 0 := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  simp only [zero_add, map_zero_of_isBigO_sq h, sub_zero]
  exact h.trans_isLittleO (isLittleO_norm_pow_id one_lt_two)
end GlobalTheory
