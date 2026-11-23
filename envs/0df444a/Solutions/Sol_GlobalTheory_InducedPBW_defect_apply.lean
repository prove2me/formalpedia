-- Prove2me | solution 1 for GlobalTheory.InducedPBW.defect_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:55.125123+00:00
-- url     : https://prove2.me/submissions/d36ff56f-0319-45fd-89d7-ec0b9bf17beb

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
variable {e c act} {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)}
  (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)
include hce
variable (hf : step e c act δ = δ)
include hf
omit hce hf [LinearOrder ι]
namespace GlobalTheory.InducedPBW
theorem _root_.solution (m : MvPolynomial ι R ⊗[R] V) (x y : g) : defect c δ m x y =
    rho c δ x (rho c δ y m) - rho c δ y (rho c δ x m) - rho c δ ⁅x, y⁆ m := rfl
end GlobalTheory.InducedPBW
