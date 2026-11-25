-- Prove2me | solution 1 for GlobalTheory.Avoid.exists_minor_ne_zero_of_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:30:05.498909+00:00
-- url     : https://prove2.me/submissions/6e86272d-db85-4e08-917b-d6d01315ac2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective
import Theorems.Thm_GlobalTheory_Avoid_exists_minor_ne_zero_of_separating

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open scoped TensorProduct Pointwise
open GlobalTheory
open GlobalTheory.Avoid
open exteriorPower
namespace GlobalTheory.Avoid
theorem _root_.solution {K V ι : Type*} [Field K] [AddCommGroup V]
    [Module K V] [Finite ι] [LinearOrder ι] (c : ι → Dual K V)
    (hc : Submodule.span K (Set.range c) = ⊤) {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Set.powersetCard ι r, pairingDual K V r (ιMulti_family K r c J) x ≠ 0 := by
  refine exists_minor_ne_zero_of_separating c (fun v hv => ?_) x hx
  rw [← forall_dual_apply_eq_zero_iff K v]
  have : Dual.eval K V v = 0 := by
    apply LinearMap.ext_on_range hc
    simpa using hv
  intro f
  simpa using DFunLike.congr_fun this f
end GlobalTheory.Avoid
