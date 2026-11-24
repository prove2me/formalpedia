-- Prove2me | solution 1 for GlobalTheory.algebraTrace_one_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:21:59.36083+00:00
-- url     : https://prove2.me/submissions/77554cbe-5c07-47fd-bc5d-af2805b3e497

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe

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
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing E]
  [Algebra R E] [Module.Free R S] [Module.Finite R S]
namespace GlobalTheory
theorem _root_.solution (x : S) :
    Algebra.trace E (E ⊗[R] S) (1 ⊗ₜ x) = algebraMap R E (Algebra.trace R S x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]
end GlobalTheory
