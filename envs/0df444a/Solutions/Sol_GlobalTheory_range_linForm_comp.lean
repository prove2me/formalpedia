-- Prove2me | solution 1 for GlobalTheory.range_linForm_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:42:24.450115+00:00
-- url     : https://prove2.me/submissions/efa7020b-4bd6-427f-bf2f-f4507c078ac7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial RingTheory.Sequence
noncomputable section
open GlobalTheory
variable {R : Type*} [CommRing R] {ι J : Type*} [Fintype J]
variable (u : J → R) {j₀ : J} (hu : IsUnit (u j₀))
namespace GlobalTheory
theorem _root_.solution {κ : Type*} (e : κ → ι) :
    Set.range (fun k => linForm u (e k)) = linForm u '' Set.range e :=
  Set.range_comp (linForm u) e
end GlobalTheory
