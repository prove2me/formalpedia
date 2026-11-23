-- Prove2me | solution 1 for GlobalTheory.InducedPBW.strip_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:53:29.153624+00:00
-- url     : https://prove2.me/submissions/bb854ba9-44a9-4341-9c03-3769c3d36b9d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_strip_apply

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
omit hce [Fintype ι] [LinearOrder ι]
namespace GlobalTheory.InducedPBW
theorem _root_.solution {s : Finset ι} {x : g} (hx : ∀ j ∈ s, c j x = 0) : strip e c s x = x := by
  rw [strip_apply, Finset.sum_eq_zero fun j hj => by rw [hx j hj, zero_smul], sub_zero]
end GlobalTheory.InducedPBW
