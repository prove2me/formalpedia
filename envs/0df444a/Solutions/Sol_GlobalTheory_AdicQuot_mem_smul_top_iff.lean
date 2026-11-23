-- Prove2me | solution 1 for GlobalTheory.AdicQuot.mem_smul_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:24:55.476663+00:00
-- url     : https://prove2.me/submissions/67445f96-59d9-46d3-b0fa-b10997846d88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AdicCompletionQuotientRingEquiv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.AdicQuot
open AdicCompletion
variable {A : Type} [CommRing A] (J q : Ideal A)
namespace GlobalTheory.AdicQuot
theorem _root_.solution (n : ℕ) (b : A ⧸ q) :
    b ∈ (J ^ n • ⊤ : Submodule A (A ⧸ q)) ↔ b ∈ (J.map (Ideal.Quotient.mk q)) ^ n := by
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, Ideal.map_pow]
  rfl
end GlobalTheory.AdicQuot
