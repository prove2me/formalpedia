-- Prove2me | solution 1 for GlobalTheory.Avoid.exists_minor_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:26:15.025175+00:00
-- url     : https://prove2.me/submissions/20706e53-f956-4147-baa9-385acdb56696

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasisMapOfLiftBaseChangeSurjective
import Theorems.Thm_GlobalTheory_Avoid_exists_minor_ne_zero_of_span

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
    [Module K V] [Finite ι] [LinearOrder ι] (c : Basis ι K (Dual K V))
    {r : ℕ} (x : ⋀[K]^r V) (hx : x ≠ 0) :
    ∃ J : Set.powersetCard ι r, pairingDual K V r (ιMulti_family K r c J) x ≠ 0 :=
  exists_minor_ne_zero_of_span c c.span_eq x hx
end GlobalTheory.Avoid
