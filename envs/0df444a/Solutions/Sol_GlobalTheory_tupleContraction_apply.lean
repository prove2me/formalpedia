-- Prove2me | solution 1 for GlobalTheory.tupleContraction_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:48:45.098927+00:00
-- url     : https://prove2.me/submissions/1220ba35-131e-4581-947d-c5943d77ecb0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_TupleDifferentialTupleDifferential

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finsupp
open GlobalTheory
variable {X : Type*}
variable (R : Type*) [Ring R] (N : Type*) [AddCommGroup N] [Module R N]
variable {R N}
namespace GlobalTheory
theorem _root_.solution (a : X) (n : ℕ) (f : (Fin (n + 1) → X) →₀ N)
    (x : Fin n → X) : tupleContraction R N a n f x = f (Fin.cons a x) := rfl
end GlobalTheory
