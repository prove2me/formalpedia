-- Prove2me | solution 1 for GlobalTheory.IsQuasiRegularSeq.map_mem_pow_smul_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:57:43.094574+00:00
-- url     : https://prove2.me/submissions/6e5e0caf-880d-4187-a761-fd9d61b80097

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsQuasiRegularSeqSelfIffLocalizationMaximal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MonomialCountAndBinomialEstimates
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsSMulRegularQuotIffMemNonZeroDivisors
import Theorems.Thm_GlobalTheory_exists_smul_mem_smul_top_of_isLocalizedModule


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R : Type*} [CommRing R] {ι : Type*} [Finite ι] {M : Type*} [AddCommGroup M] [Module R M]
  {f : ι → R}
namespace GlobalTheory
namespace IsQuasiRegularSeq
theorem _root_.solution (h : IsQuasiRegularSeq M f) (T : Submonoid R)
    (hT : ∀ t ∈ T, IsSMulRegular (M ⧸ (Ideal.span (Set.range f) • ⊤ : Submodule R M)) t)
    {N : Type*} [AddCommGroup N] [Module R N] (g : M →ₗ[R] N) [IsLocalizedModule T g] (a : ℕ)
    (m : M) : g m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R N) ↔
      m ∈ (Ideal.span (Set.range f) ^ a • ⊤ : Submodule R M) := by
  refine ⟨fun hm => ?_, fun hm => Submodule.smul_top_le_comap_smul_top _ g hm⟩
  obtain ⟨s, hs, hsm⟩ := exists_smul_mem_smul_top_of_isLocalizedModule T g _ hm
  exact h.mem_pow_smul_top_of_smul_mem (hT s hs) a hsm
end IsQuasiRegularSeq
end GlobalTheory
