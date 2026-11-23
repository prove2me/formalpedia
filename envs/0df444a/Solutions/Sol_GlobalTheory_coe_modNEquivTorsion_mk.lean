-- Prove2me | solution 1 for GlobalTheory.coe_modNEquivTorsion_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:07:56.616423+00:00
-- url     : https://prove2.me/submissions/5e109156-726b-4f05-b0de-e84e8b0ca0a4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueRealLinearOfEventuallyAddModDiscrete

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology Set
open GlobalTheory
variable (K : Type*) [DivisionRing K] [CharZero K] {M : Type*} [AddCommGroup M] [Module K M]
  (Λ : Submodule ℤ M) (n : ℕ) [NeZero n]
namespace GlobalTheory
theorem _root_.solution (x : Λ) :
    (modNEquivTorsion K Λ n (Submodule.Quotient.mk x) : M ⧸ Λ) =
      Submodule.Quotient.mk ((n : K)⁻¹ • (x : M)) := rfl
end GlobalTheory
