-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_of_isRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:41:58.761575+00:00
-- url     : https://prove2.me/submissions/60fcd7d9-7155-4e15-a5fc-615e1cfa10c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence
open GlobalTheory
variable {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution {n : ℕ} {f : Fin n → R}
    (h : RingTheory.Sequence.IsRegular M (List.ofFn f)) : IsQuasiRegularSeq M f :=
  isQuasiRegularSeq_of_isWeaklyRegular h.toIsWeaklyRegular
end GlobalTheory
