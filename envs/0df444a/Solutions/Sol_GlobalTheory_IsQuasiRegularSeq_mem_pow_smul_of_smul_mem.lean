-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.mem_pow_smul_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:00:28.678506+00:00
-- url     : https://prove2.me/submissions/1c5126a7-d622-4f0d-9f75-31ecbb628768

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_mem_pow_succ_smul_of_smul_mem

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
    (i : ι) {a : ℕ} {m : M}
    (hfm : f i • m ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M)) :
    m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
  induction a with
  | zero => simp
  | succ a ih =>
    exact h.mem_pow_succ_smul_of_smul_mem i (ih (powGr.pow_succ_smul_le _ M _ hfm)) hfm
end IsQuasiRegularSeq
end GlobalTheory
