-- Prove2me | solution 1 for GroundTheory.PAdicHodge.norm_tateTrace_le_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:42:36.390881+00:00
-- url     : https://prove2.me/submissions/bdd1796e-68c1-436e-93c9-960582dd07e2

import Mathlib
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceTower
import Definitions.Def_GroundTheory_PAdicHodge_NormalizedTraceClosure
import Definitions.Def_GroundTheory_PAdicHodge_CyclotomicTower
import Definitions.Def_GroundTheory_PAdicHodge_TateNormalizedTrace
import Theorems.Thm_GroundTheory_PAdicHodge_norm_tateTrace_le

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
open IntermediateField Module Set
noncomputable section
variable {p : ℕ} [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
  [FiniteDimensional ℚ_[p] K]
variable {K}
namespace GroundTheory.PAdicHodge
theorem _root_.solution (n : ℕ) : ∀ y ∈ cyclotomicLimit K,
    ‖tateTrace K n y‖ ≤ tateBound K * ‖y‖ :=
  fun _ hy => norm_tateTrace_le K n hy
end GroundTheory.PAdicHodge
