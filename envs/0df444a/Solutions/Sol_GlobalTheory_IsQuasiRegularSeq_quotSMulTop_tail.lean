-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.quotSMulTop_tail
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T00:12:44.837997+00:00
-- url     : https://prove2.me/submissions/34cdc122-7754-440c-a511-3451a9c88ef8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_quotSMulTop
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_comp_equiv


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
namespace IsQuasiRegularSeq
theorem _root_.solution {n : ℕ} {f : Fin (n + 1) → R}
    (h : IsQuasiRegularSeq M f) :
    IsQuasiRegularSeq (QuotSMulTop (f 0) M) fun i : Fin n => f i.succ :=
  (h.comp_equiv (finSuccEquiv n).symm).quotSMulTop
end IsQuasiRegularSeq
end GlobalTheory
