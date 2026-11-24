-- Prove2me | solution 1 for GlobalTheory.InducedPBW.comm_high
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:14:20.206146+00:00
-- url     : https://prove2.me/submissions/27ed6e23-ec71-42e7-b71e-fd908fa30b5d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_rho_apply
import Theorems.Thm_GlobalTheory_InducedPBW_strip_eq
import Theorems.Thm_GlobalTheory_InducedPBW_rho_e_le
import Theorems.Thm_GlobalTheory_InducedPBW_le_support_add

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
namespace GlobalTheory.InducedPBW
theorem _root_.solution (i : ι) (J : ι →₀ ℕ) (hJ : ∀ j ∈ J.support, i ≤ j) (x : g)
    (hx : ∀ j, j ≤ i → c j x = 0) (v : V) :
    rho c δ x (rho c δ (e i) (zv J v)) =
      rho c δ (e i) (rho c δ x (zv J v)) + rho c δ ⁅x, e i⁆ (zv J v) := by
  rw [rho_e_le hce hf i J hJ, rho_apply c δ x, rho_apply c δ x, map_add]
  conv_lhs => rw [← hf]
  rw [step_succ e c act δ i J hJ, straighten_apply,
    strip_eq (fun j hj => hx j (by simpa using hj)), ← add_assoc]
  congr 2
  rw [mulLin_apply, mulLin_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ≤ i
  · simp [hx j hj]
  · rw [map_smul, mulX_zv, mulX_zv,
      rho_e_le hce hf i _ (le_support_add hJ (not_le.mp hj).le), add_left_comm]
end GlobalTheory.InducedPBW
