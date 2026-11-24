-- Prove2me | solution 1 for GlobalTheory.IsSaturatedSubmodule.eq_of_le_of_finrank_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:34:47.052846+00:00
-- url     : https://prove2.me/submissions/1f9b739c-87c5-4bbf-8830-ce1b0119ce6b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_le_saturation_iff_finrank_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] [IsDomain R] {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
namespace IsSaturatedSubmodule
theorem _root_.solution [Module.Finite R M] {N P : Submodule R M}
    (hN : IsSaturatedSubmodule N) (h : N ≤ P) (hr : Module.finrank R N = Module.finrank R P) :
    N = P := le_antisymm h (((le_saturation_iff_finrank_eq h).2 hr).trans hN.saturation_eq.le)
end IsSaturatedSubmodule
end GlobalTheory
