-- Prove2me | solution 1 for GlobalTheory.AdicNoeth.isNoetherianRing_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:24:38.314017+00:00
-- url     : https://prove2.me/submissions/926fda5b-d5e9-4241-b7fe-298e28da9a96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGradedRingKernelLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsNoetherianRingOfIsAdicComplete
import Theorems.Thm_GlobalTheory_AdicNoeth_exists_leading_generators
import Theorems.Thm_GlobalTheory_AdicNoeth_mem_span_of_leading

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.AdicNoeth
namespace GlobalTheory.AdicNoeth
theorem _root_.solution : ∀ (R : Type) [CommRing R] (I : Ideal R), I.FG →
    IsAdicComplete I R → IsNoetherianRing (R ⧸ I) → IsNoetherianRing R := by
  intro R _ I hI hc hq
  refine isNoetherianRing_iff.mpr ⟨fun J => ?_⟩
  obtain ⟨ι, _, f, d, hf, hlead⟩ := exists_leading_generators I hI J
  have hJ : J = Ideal.span (Set.range f) := le_antisymm
    (fun g hg => mem_span_of_leading I J f d hf hlead g hg)
    (Ideal.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hf i))
  rw [hJ]
  exact Submodule.fg_span (Set.finite_range f)
end GlobalTheory.AdicNoeth
