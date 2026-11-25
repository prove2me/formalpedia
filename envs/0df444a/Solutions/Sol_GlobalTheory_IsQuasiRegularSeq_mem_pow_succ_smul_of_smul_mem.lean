-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.mem_pow_succ_smul_of_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:53:34.416436+00:00
-- url     : https://prove2.me/submissions/076ce48f-0187-4c70-a88a-e714cbfb73f8

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
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι]
variable {M : Type*} [AddCommGroup M] [Module R M]
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution {f : ι → R} (h : IsQuasiRegularSeq M f)
    (i : ι) {a : ℕ} {m : M} (hm : m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M))
    (hfm : f i • m ∈ (Ideal.span (Set.range f) ^ (a + 2) • ⊤ : Submodule R M)) :
    m ∈ (Ideal.span (Set.range f) ^ (a + 1) • ⊤ : Submodule R M) := by
  obtain ⟨c, rfl⟩ := (mem_pow_smul_top_iff f a m).mp hm
  refine sum_monoVal_smul_mem_pow_succ f fun γ => ?_
  have hinj := MonoDeg.mulVar_injective i a
  have := h (a + 1) (Function.extend (MonoDeg.mulVar i) c 0) (by
    rw [← Fintype.sum_of_injective _ hinj (fun γ => f i • monoVal f γ.1 • c γ)]
    · rwa [Finset.smul_sum] at hfm
    · intro α hα
      rw [Function.extend_apply' _ _ _ hα]
      simp
    · intro γ
      rw [hinj.extend_apply, monoVal_mulVar, mul_smul]) (MonoDeg.mulVar i γ)
  rwa [hinj.extend_apply] at this
end IsQuasiRegularSeq
end GlobalTheory
