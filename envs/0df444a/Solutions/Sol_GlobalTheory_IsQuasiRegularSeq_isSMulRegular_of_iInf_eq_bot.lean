-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.isSMulRegular_of_iInf_eq_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:05:59.759463+00:00
-- url     : https://prove2.me/submissions/fae85219-ba63-4dcc-9b09-570c673e81ae

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_mem_pow_smul_of_smul_mem

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
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution {f : ι → R} (h : IsQuasiRegularSeq M f)
    (hsep : (⨅ a : ℕ, Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) = ⊥) (i : ι) :
    IsSMulRegular M (f i) := by
  refine .of_right_eq_zero_of_smul fun m hm => ?_
  rw [← Submodule.mem_bot R, ← hsep, Submodule.mem_iInf]
  exact fun a => h.mem_pow_smul_of_smul_mem i (by rw [hm]; exact zero_mem _)
end IsQuasiRegularSeq
end GlobalTheory
