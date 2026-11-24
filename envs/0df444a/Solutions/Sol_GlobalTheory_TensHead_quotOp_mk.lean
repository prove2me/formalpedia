-- Prove2me | solution 1 for GlobalTheory.TensHead.quotOp_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:24:56.784201+00:00
-- url     : https://prove2.me/submissions/a319579e-6c97-4de0-bb6f-1e2139e4ed34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LeKerOfLocalFiniteLengthToSimpleStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SimpleOver
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EqTopOfPureTensorsOfFactorGenerators
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_PiTensorMaximalStableContainsFactorKernel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.TensHead
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.TensHead
theorem _root_.solution (N : Submodule ℂ V) (f : Module.End ℂ V) (h : ∀ x ∈ N, f x ∈ N) (x : V) :
    quotOp N f (N.mkQ x) = N.mkQ (f x) := by
  have h' : N ≤ N.comap f := fun x hx => h x hx
  unfold quotOp
  rw [dif_pos h']
  simp
end GlobalTheory.TensHead
