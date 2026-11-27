-- Prove2me | solution 1 for GlobalTheory.isRegular_ofFn_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:42:11.058081+00:00
-- url     : https://prove2.me/submissions/c5129e1a-2ac8-411f-80c1-14968051c1c8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_isRegular_map_X

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
variable {R : Type*} [CommRing R] {σ : Type*}
namespace GlobalTheory
theorem _root_.solution [Nontrivial R] {n : ℕ} {e : Fin n → σ} (he : Function.Injective e) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (List.ofFn fun k => (X (e k) : MvPolynomial σ R)) := by
  have := isRegular_map_X (R := R) (List.nodup_ofFn.2 he)
  rwa [List.map_ofFn] at this
end GlobalTheory
