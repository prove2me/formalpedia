-- Prove2me | solution 1 for GlobalTheory.InducedPBW.defect_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:33:50.792861+00:00
-- url     : https://prove2.me/submissions/7173b851-3594-46bf-a589-5cdcdc678db9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DegreeSingleAdd
import Theorems.Thm_GlobalTheory_InducedPBW_strip_apply
import Theorems.Thm_GlobalTheory_InducedPBW_c_strip
import Theorems.Thm_GlobalTheory_InducedPBW_comm_high
import Theorems.Thm_GlobalTheory_InducedPBW_defect_apply
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
namespace GlobalTheory.InducedPBW
theorem _root_.solution (i : ι) (J : ι →₀ ℕ) (hJ : ∀ j ∈ J.support, i ≤ j) (x : g) (v : V) :
    defect c δ (zv J v) x (e i) = 0 := by
  have hx : x = strip e c Finset.univ x + ∑ j, c j x • e j := by simp [strip_apply]
  rw [hx, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, Finset.sum_eq_zero, add_zero]
  · rw [defect_apply, comm_high hce hf i J hJ _ fun j _ => c_strip hce (Finset.mem_univ _) x]
    abel
  · intro j _
    rw [map_smul, LinearMap.smul_apply]
    suffices h : defect c δ (zv J v) (e j) (e i) = 0 by rw [h, smul_zero]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [defect_apply, comm_high hce hf i J hJ _ fun k hk => by
        rw [hce, if_neg (hk.trans_lt h).ne]]
      abel
    · simp [defect_apply]
    · rw [defect_swap, defect_apply, comm_high hce hf j J (fun k hk => h.le.trans (hJ k hk)) _
        fun k hk => by rw [hce, if_neg (hk.trans_lt h).ne]]
      abel
end GlobalTheory.InducedPBW
