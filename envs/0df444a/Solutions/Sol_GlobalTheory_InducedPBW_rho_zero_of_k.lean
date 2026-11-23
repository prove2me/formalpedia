-- Prove2me | solution 1 for GlobalTheory.InducedPBW.rho_zero_of_k
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:55:55.186184+00:00
-- url     : https://prove2.me/submissions/efbbe22b-e45b-4b00-bbd7-1dbe4c415b40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_rho_apply
import Theorems.Thm_GlobalTheory_InducedPBW_strip_eq

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
omit hce
namespace GlobalTheory.InducedPBW
theorem _root_.solution (x : g) (hx : ∀ j, c j x = 0) (v : V) :
    rho c δ x (zv 0 v) = zv 0 (act x v) := by
  rw [rho_apply, ← hf, step_zero, strip_eq fun j _ => hx j, mulLin_apply]
  simp [hx]
end GlobalTheory.InducedPBW
