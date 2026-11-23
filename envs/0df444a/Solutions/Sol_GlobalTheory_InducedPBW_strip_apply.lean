-- Prove2me | solution 1 for GlobalTheory.InducedPBW.strip_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:55.083915+00:00
-- url     : https://prove2.me/submissions/64e21632-5a83-4871-8736-7ad9d7907ae6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.InducedPBW
variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]
variable {g : Type*} [LieRing g] [LieAlgebra R g]
variable [Fintype ι] [LinearOrder ι] (e : ι → g) (c : ι → g →ₗ[R] R) (act : g →ₗ[R] Module.End R V)
omit [Fintype ι] [LinearOrder ι]
namespace GlobalTheory.InducedPBW
theorem _root_.solution (s : Finset ι) (x : g) : strip e c s x = x - ∑ j ∈ s, c j x • e j := by
  simp [strip, LinearMap.sum_apply]
end GlobalTheory.InducedPBW
