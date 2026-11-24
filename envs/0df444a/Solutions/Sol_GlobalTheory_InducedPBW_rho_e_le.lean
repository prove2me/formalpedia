-- Prove2me | solution 1 for GlobalTheory.InducedPBW.rho_e_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:58:32.94266+00:00
-- url     : https://prove2.me/submissions/3c2a6276-b22a-4016-b38d-c698c11cd695

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_rho_apply
import Theorems.Thm_GlobalTheory_InducedPBW_strip_e_mem
import Theorems.Thm_GlobalTheory_InducedPBW_mulLin_e

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
theorem _root_.solution (i : ι) (α : ι →₀ ℕ) (h : ∀ j ∈ α.support, i ≤ j) (v : V) :
    rho c δ (e i) (zv α v) = zv (Finsupp.single i 1 + α) v := by
  rw [rho_apply, mulLin_e hce, mulX_zv, ← hf]
  rcases exponent_cases α with rfl | ⟨j, J, hJ, rfl⟩
  · rw [step_zero, strip_e_mem hce (Finset.mem_univ _)]
    simp
  · have hij : i ≤ j := h j (by simp)
    rw [step_succ e c act δ j J hJ, straighten_apply, strip_e_mem hce (by simpa using hij)]
    simp
end GlobalTheory.InducedPBW
