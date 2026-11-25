-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.isWeaklyRegular
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:56:11.132159+00:00
-- url     : https://prove2.me/submissions/0209c2f3-4955-4077-a740-a26512ceb443

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_isSMulRegular_of_iInf_eq_bot
import Theorems.Thm_GlobalTheory_IsQuasiRegularSeq_quotSMulTop_tail

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
theorem _root_.solution [IsNoetherianRing R] [Module.Finite R M] {n : ℕ}
    {f : Fin n → R} (h : IsQuasiRegularSeq M f) (hf : ∀ i, f i ∈ (⊥ : Ideal R).jacobson) :
    IsWeaklyRegular M (List.ofFn f) := by
  induction n generalizing M with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, isWeaklyRegular_cons_iff]
    refine ⟨h.isSMulRegular_of_iInf_eq_bot (Ideal.iInf_pow_smul_eq_bot_of_le_jacobson _ ?_) 0,
      ih h.quotSMulTop_tail fun i => hf _⟩
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    exact hf i
end IsQuasiRegularSeq
end GlobalTheory
