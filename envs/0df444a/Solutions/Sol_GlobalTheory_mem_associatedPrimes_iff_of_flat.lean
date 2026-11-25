-- Prove2me | solution 1 for GlobalTheory.mem_associatedPrimes_iff_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:36.390159+00:00
-- url     : https://prove2.me/submissions/ffc7caf3-c6fc-4cbe-867c-a47e20dc3e3f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Theorems.Thm_GlobalTheory_mem_associatedPrimes_iff_of_flat_module
import Theorems.Thm_GlobalTheory_mem_associatedPrimes_tensor_residueField_iff

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
variable [Module B M] [IsScalarTower A B M] [Module.Flat A M]
variable [Module.Flat A B]
namespace GlobalTheory
theorem _root_.solution [IsNoetherianRing A] (q : Ideal B) [q.IsPrime] :
    q ∈ associatedPrimes B B ↔ q.under A ∈ associatedPrimes A A ∧
      ∃ Q ∈ associatedPrimes ((q.under A).Fiber B) ((q.under A).Fiber B),
        Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[A] (q.under A).Fiber B) = q := by
  rw [mem_associatedPrimes_iff_of_flat_module (A := A),
    mem_associatedPrimes_tensor_residueField_iff]
end GlobalTheory
