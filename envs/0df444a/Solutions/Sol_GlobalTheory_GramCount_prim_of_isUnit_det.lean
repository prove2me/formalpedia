-- Prove2me | solution 1 for GlobalTheory.GramCount.prim_of_isUnit_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T17:11:14.235649+00:00
-- url     : https://prove2.me/submissions/d543772a-53e6-4af4-9a80-bc9d04fb7152

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Theorems.Thm_GlobalTheory_GramCount_ip_smul_right
import Theorems.Thm_GlobalTheory_GramCount_ip_sum_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}
namespace GlobalTheory.GramCount
theorem _root_.solution (hc : ∀ u, c (c u) = u) {m : ℕ} (x y : Fin m → Fin n → A)
    (h : IsUnit (Matrix.of fun a b => ip c (x a) (y b)).det) : Prim c x := by

  unfold Prim
  refine ⟨fun b => ∑ k, c ((Matrix.of fun a b => ip c (x a) (y b))⁻¹ k b) • y k,
    fun a b => ?_⟩
  have h1 := congrFun (congrFun (Matrix.mul_nonsing_inv _ h) a) b
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simp only [Matrix.of_apply] at h1
  rw [ip_sum_right]
  simp only [ip_smul_right, hc]
  rw [← h1]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _
end GlobalTheory.GramCount
