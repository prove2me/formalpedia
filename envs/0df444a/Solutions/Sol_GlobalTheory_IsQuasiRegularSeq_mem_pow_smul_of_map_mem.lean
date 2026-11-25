-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.mem_pow_smul_of_map_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:58:39.982987+00:00
-- url     : https://prove2.me/submissions/c4d93fea-bbd2-428d-85e0-4aed736d6d15

import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_ChainConnInDim
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularIffIsQuasiRegularSeqOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsIsRegularQuotSMulTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsRegularOfSupportDimQuotientAddLengthLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open RingTheory.Sequence IsLocalRing TensorProduct
open GlobalTheory
variable {A : Type*} [CommRing A] {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution {ι : Type*} [Finite ι] {f : ι → A}
    (h : IsQuasiRegularSeq M f) {F : Type*} [AddCommGroup F] [Module A F] (g : F →ₗ[A] M)
    (hg : ∀ z, g z ∈ (Ideal.span (Set.range f) • ⊤ : Submodule A M) →
      z ∈ (Ideal.span (Set.range f) • ⊤ : Submodule A F)) (n : ℕ) (z : F)
    (hz : g z ∈ (Ideal.span (Set.range f) ^ n • ⊤ : Submodule A M)) :
    z ∈ (Ideal.span (Set.range f) ^ n • ⊤ : Submodule A F) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨c, rfl⟩ := (mem_pow_smul_top_iff f n z).mp (ih (powGr.pow_succ_smul_le _ M n hz))
    refine sum_monoVal_smul_mem_pow_succ f fun α => hg _ ?_
    exact h n (fun α => g (c α)) (by simpa using hz) α
end IsQuasiRegularSeq
end GlobalTheory
