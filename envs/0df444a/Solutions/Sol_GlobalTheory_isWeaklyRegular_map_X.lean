-- Prove2me | solution 1 for GlobalTheory.isWeaklyRegular_map_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:41:26.607186+00:00
-- url     : https://prove2.me/submissions/5a8fc1d8-166e-4be2-8fd4-bb8e567ac075

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_isWeaklyRegular_map_C_append_map_X

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
theorem _root_.solution {l : List σ} (hl : l.Nodup) :
    IsWeaklyRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)) := by
  simpa using isWeaklyRegular_map_C_append_map_X (IsWeaklyRegular.nil R R) hl
end GlobalTheory
