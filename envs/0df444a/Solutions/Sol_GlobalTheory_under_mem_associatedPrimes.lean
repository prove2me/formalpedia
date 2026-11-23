-- Prove2me | solution 1 for GlobalTheory.under_mem_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:49.024091+00:00
-- url     : https://prove2.me/submissions/97585d89-bddb-474e-a511-4921202a6d21

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution [Module B M] [IsScalarTower A B M] {q : Ideal B}
    (hq : q ∈ associatedPrimes B M) : q.under A ∈ associatedPrimes A M := by
  obtain ⟨hq', x, hx⟩ := hq
  refine ⟨hq'.under A, x, ?_⟩
  ext a
  rw [Ideal.under_def, Ideal.mem_comap, hx]
  simp only [Ideal.mem_radical_iff, Submodule.mem_colon_singleton, Submodule.mem_bot, ← map_pow,
    algebraMap_smul]
end GlobalTheory
