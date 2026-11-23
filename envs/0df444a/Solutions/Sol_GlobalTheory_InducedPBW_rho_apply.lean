-- Prove2me | solution 1 for GlobalTheory.InducedPBW.rho_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:47:54.383774+00:00
-- url     : https://prove2.me/submissions/4f3b632c-ce11-45fa-9e22-18c1629b5bbb

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
omit [LinearOrder ι]
namespace GlobalTheory.InducedPBW
theorem _root_.solution (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (x m) :
    rho c δ x m = mulLin c x m + δ x m := rfl
end GlobalTheory.InducedPBW
