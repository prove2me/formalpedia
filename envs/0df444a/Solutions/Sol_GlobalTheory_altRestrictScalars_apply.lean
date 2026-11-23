-- Prove2me | solution 1 for GlobalTheory.altRestrictScalars_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:26.264+00:00
-- url     : https://prove2.me/submissions/c5fd2ecc-dcf6-40ef-9f3a-f70a1b2da6ef

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open scoped BigOperators
variable (A : Type*) {B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M]
  [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] {D : ℕ}
namespace GlobalTheory
theorem _root_.solution (ω : M [⋀^Fin D]→ₗ[B] N) (v : Fin D → M) :
    altRestrictScalars A ω v = ω v := rfl
end GlobalTheory
