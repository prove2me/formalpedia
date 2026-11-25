-- Prove2me | solution 1 for GlobalTheory.LevDesc.algOp_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:59:49.334192+00:00
-- url     : https://prove2.me/submissions/db306f72-2ec4-460f-a859-9d9d437ff6a6

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
theorem _root_.solution [Fintype G] (e : MonoidAlgebra K G) (x : R) :
    algOp st e x = ∑ g, e.coeff g • st g⁻¹ x := by
  rw [algOp, Finsupp.linearCombination_apply,
    Finsupp.sum_fintype _ (fun i a => a • (st i⁻¹).toLinearMap) (fun _ => zero_smul _ _), LinearMap.sum_apply]
  rfl
end GlobalTheory.LevDesc
