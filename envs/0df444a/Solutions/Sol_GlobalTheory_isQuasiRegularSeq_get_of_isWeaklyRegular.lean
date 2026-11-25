-- Prove2me | solution 1 for GlobalTheory.isQuasiRegularSeq_get_of_isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:34.467437+00:00
-- url     : https://prove2.me/submissions/61eb819a-1541-4ba9-a494-981121cb8a3c

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
theorem _root_.solution {rs : List R} (h : IsWeaklyRegular M rs) :
    IsQuasiRegularSeq M rs.get :=
  isQuasiRegularSeq_of_isWeaklyRegular (by rwa [List.ofFn_get])
end GlobalTheory
