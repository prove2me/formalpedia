-- Prove2me | solution 1 for GlobalTheory.subsingleton_of_countable_realModule
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:58.300094+00:00
-- url     : https://prove2.me/submissions/491fb211-eba0-48e0-974c-e6ec3e2f60e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable {M N : Type*} [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
namespace GlobalTheory
theorem _root_.solution (M : Type*) [AddCommGroup M] [Module ℝ M]
    [Countable M] : Subsingleton M := by
  refine subsingleton_of_forall_eq 0 fun v ↦ by_contra fun hv ↦ ?_
  exact not_countable (α := ℝ) (smul_left_injective ℝ hv).countable
end GlobalTheory
