-- Prove2me | solution 1 for GlobalTheory.SymDesc.injective_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:48:13.277016+00:00
-- url     : https://prove2.me/submissions/5d859208-1a8d-4d51-823d-c4c0b3df349d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MemRangeOfForallAlgHomEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DescendElementOfFieldEqualizerFaithfullyFlat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.SymDesc
variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Algebra R R₁]
namespace GlobalTheory.SymDesc
theorem _root_.solution (Q : Ideal R₁) (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    Function.Injective (algebraMap R (R₁ ⧸ Q)) := by
  rw [injective_iff_map_eq_zero]
  intro r hr
  have : r ∈ Q.comap (algebraMap R R₁) := by
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
    exact hr
  rwa [hQ, Ideal.mem_bot] at this
end GlobalTheory.SymDesc
