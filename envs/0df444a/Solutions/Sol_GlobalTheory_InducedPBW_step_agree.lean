-- Prove2me | solution 1 for GlobalTheory.InducedPBW.step_agree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:41:49.289794+00:00
-- url     : https://prove2.me/submissions/38e65f46-0459-48fe-8931-64aceef6ab2a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_eq_on_degLt
import Theorems.Thm_GlobalTheory_InducedPBW_rho_apply

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
namespace GlobalTheory.InducedPBW
theorem _root_.solution {δ δ' : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)} (h : Pres δ) {n : ℕ}
    (ha : ∀ x, ∀ m ∈ degLt R ι V n, δ x m = δ' x m) :
    ∀ x, ∀ m ∈ degLt R ι V (n + 1), step e c act δ x m = step e c act δ' x m := by
  intro x
  refine eq_on_degLt _ _ fun α v hα => ?_
  rcases exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩
  · rw [step_zero, step_zero]
  · rw [step_succ e c act δ i J hJ, step_succ e c act δ' i J hJ, straighten_apply,
      straighten_apply]
    rw [degree_single_add] at hα
    have hz : zv J v ∈ degLt R ι V n := zv_mem (by omega) v
    simp only [rho_apply]
    rw [ha _ _ (h _ _ _ hz), ha _ _ hz, ha _ _ hz]
end GlobalTheory.InducedPBW
