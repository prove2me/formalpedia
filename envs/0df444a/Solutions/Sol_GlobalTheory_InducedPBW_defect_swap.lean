-- Prove2me | solution 1 for GlobalTheory.InducedPBW.defect_swap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:54:25.390511+00:00
-- url     : https://prove2.me/submissions/fd262a35-ad66-4da5-8813-902dd1b4acc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_defect_apply

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
theorem _root_.solution (m : MvPolynomial ι R ⊗[R] V) (x y : g) :
    defect c δ m x y = - defect c δ m y x := by
  rw [defect_apply, defect_apply, ← lie_skew x y, map_neg, LinearMap.neg_apply]
  abel
end GlobalTheory.InducedPBW
