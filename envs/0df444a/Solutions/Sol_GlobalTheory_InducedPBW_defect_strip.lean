-- Prove2me | solution 1 for GlobalTheory.InducedPBW.defect_strip
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:47.575903+00:00
-- url     : https://prove2.me/submissions/4b5227f0-f970-42b9-8fb6-61fcbd7827b8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_strip_apply
import Theorems.Thm_GlobalTheory_InducedPBW_defect_swap

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
theorem _root_.solution (m : MvPolynomial ι R ⊗[R] V) (s : Finset ι)
    (h : ∀ j ∈ s, ∀ x, defect c δ m x (e j) = 0) (x y : g) :
    defect c δ m x y = defect c δ m (strip e c s x) (strip e c s y) := by
  have h' : ∀ j ∈ s, ∀ x, defect c δ m (e j) x = 0 := fun j hj x => by
    rw [defect_swap, h j hj, neg_zero]
  rw [strip_apply e c s y, map_sub, map_sum, Finset.sum_eq_zero fun j hj => by
    rw [map_smul, h j hj, smul_zero], sub_zero, strip_apply, map_sub, map_sum,
    LinearMap.sub_apply, LinearMap.sum_apply, Finset.sum_eq_zero fun j hj => by
    rw [map_smul, LinearMap.smul_apply, h' j hj, smul_zero], sub_zero]
end GlobalTheory.InducedPBW
