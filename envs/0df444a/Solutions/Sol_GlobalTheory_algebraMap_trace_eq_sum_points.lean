-- Prove2me | solution 1 for GlobalTheory.algebraMap_trace_eq_sum_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:27:05.701121+00:00
-- url     : https://prove2.me/submissions/57c52c25-7ed6-4808-91a8-235b15b8457c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Theorems.Thm_GlobalTheory_algebraTrace_pi_apply
import Theorems.Thm_GlobalTheory_algebraTrace_one_tmul
import Theorems.Thm_GlobalTheory_exists_algEquiv_points

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable [Module.Free R S]
variable {E} {ι : Type*} [Fintype ι]
variable [Module.Finite R S]
namespace GlobalTheory
theorem _root_.solution (P : ι ≃ (S →ₐ[R] E)) (x : S) :
    algebraMap R E (Algebra.trace R S x) = ∑ j, P j x := by
  obtain ⟨e, he⟩ := exists_algEquiv_points P
  rw [← algebraTrace_one_tmul, ← Algebra.trace_eq_of_algEquiv e, algebraTrace_pi_apply]
  simp [he]
end GlobalTheory
