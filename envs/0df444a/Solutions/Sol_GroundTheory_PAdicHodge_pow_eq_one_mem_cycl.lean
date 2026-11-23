-- Prove2me | solution 1 for GroundTheory.PAdicHodge.pow_eq_one_mem_cycl
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:16.572793+00:00
-- url     : https://prove2.me/submissions/1ed132b2-9183-4df3-95c0-ad3c25b90132

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTrace
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicField

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
open IntermediateField Polynomial
noncomputable section
variable (p : ℕ) [Fact p.Prime]
variable {p}
namespace GroundTheory.PAdicHodge
theorem _root_.solution {n : ℕ} {x : PadicAlgCl p} (hx : x ^ (p ^ n) = 1) : x ∈ cycl p n :=
  subset_adjoin _ _ hx
end GroundTheory.PAdicHodge
