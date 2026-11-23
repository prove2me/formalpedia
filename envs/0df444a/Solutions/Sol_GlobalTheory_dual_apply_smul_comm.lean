-- Prove2me | solution 1 for GlobalTheory.dual_apply_smul_comm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:24.196583+00:00
-- url     : https://prove2.me/submissions/0905766a-1bed-41a1-8b07-78c4cc9bdc7e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

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
variable {A : Type*} [CommRing A]
variable {M : Type*} [AddCommGroup M] [Module A M]
namespace GlobalTheory
theorem _root_.solution [Module.Invertible A M] (f : Module.Dual A M) (x y : M) :
    f x • y = f y • x := by
  have := congrArg (fun z ↦ TensorProduct.lid A M (f.rTensor M z))
    (Module.Invertible.tmul_comm (R := A) (m₁ := x) (m₂ := y))
  simpa using this
end GlobalTheory
