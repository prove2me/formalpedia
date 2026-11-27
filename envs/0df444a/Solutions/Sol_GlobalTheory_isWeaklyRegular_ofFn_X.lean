-- Prove2me | solution 1 for GlobalTheory.isWeaklyRegular_ofFn_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:39:08.574903+00:00
-- url     : https://prove2.me/submissions/b627a28d-2c84-44b9-85e8-1e510575485b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_isWeaklyRegular_map_X

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
theorem _root_.solution {n : ℕ} {e : Fin n → σ} (he : Function.Injective e) :
    IsWeaklyRegular (MvPolynomial σ R) (List.ofFn fun k => (X (e k) : MvPolynomial σ R)) := by
  have := isWeaklyRegular_map_X (R := R) (List.nodup_ofFn.2 he)
  rwa [List.map_ofFn] at this
end GlobalTheory
