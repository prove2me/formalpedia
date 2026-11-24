-- Prove2me | solution 1 for GlobalTheory.TopForm.extProj_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:32:54.403801+00:00
-- url     : https://prove2.me/submissions/3e65040f-2246-4f91-b12b-9f2d09791d1b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange

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
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
namespace GlobalTheory.TopForm
theorem _root_.solution (D : ℕ) (x : ⋀[A]^D M) : extProj A M D x = x := by
  change (DirectSum.decompose (fun i => ⋀[A]^i M) (x : ExteriorAlgebra A M)) D = x
  rw [DirectSum.decompose_coe, DirectSum.of_eq_same]
end GlobalTheory.TopForm
