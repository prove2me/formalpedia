-- Prove2me | solution 1 for GlobalTheory.LevDesc.algOp_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:51.368216+00:00
-- url     : https://prove2.me/submissions/147e7587-c527-4d64-a85c-1156fed5a85c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R : Type} [Group G] [Field K] [CommRing R] [Algebra K R]
variable (st : G → R →ₐ[K] R)
namespace GlobalTheory.LevDesc
theorem _root_.solution {C : Submodule K R} (hC : ∀ h, ∀ x ∈ C, st h x ∈ C) (e : MonoidAlgebra K G) {x : R} (hx : x ∈ C) :
    algOp st e x ∈ C := by
  rw [algOp, Finsupp.linearCombination_apply, Finsupp.sum, LinearMap.sum_apply]
  exact C.sum_mem fun g _ => C.smul_mem _ (hC _ x hx)
end GlobalTheory.LevDesc
