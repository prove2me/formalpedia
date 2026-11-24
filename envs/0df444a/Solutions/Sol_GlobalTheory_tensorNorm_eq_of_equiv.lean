-- Prove2me | solution 1 for GlobalTheory.tensorNorm_eq_of_equiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:46:02.808809+00:00
-- url     : https://prove2.me/submissions/ccca508f-2f29-4c70-be28-bebd42f193ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_tprod_comp_perm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable {M : Type*} [AddCommGroup M] [Module A M] [DistribMulAction G M] {ι : Type*}
omit [MulSemiringAction G A]
namespace GlobalTheory
theorem _root_.solution [Finite G] [Module.Invertible A M] (κ κ' : ι ≃ G) (x : M) :
    tensorNorm A κ x = tensorNorm A κ' x := by
  haveI : Finite ι := .of_equiv _ κ.symm
  rw [tensorNorm, tensorNorm, ← tprod_comp_perm (fun i ↦ κ' i • x) (κ.trans κ'.symm)]
  simp
end GlobalTheory
