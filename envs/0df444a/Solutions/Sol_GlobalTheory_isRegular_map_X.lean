-- Prove2me | solution 1 for GlobalTheory.isRegular_map_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:48:43.72678+00:00
-- url     : https://prove2.me/submissions/ca875731-efd6-4d12-9a06-e4906ce314eb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Theorems.Thm_GlobalTheory_isRegular_map_C_append_map_X

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
theorem _root_.solution [Nontrivial R] {l : List σ} (hl : l.Nodup) :
    RingTheory.Sequence.IsRegular (MvPolynomial σ R) (l.map X : List (MvPolynomial σ R)) := by
  simpa using isRegular_map_C_append_map_X (RingTheory.Sequence.IsRegular.nil R R) hl
end GlobalTheory
