-- Prove2me | solution 1 for GlobalTheory.LatPair.Model.isAdj_sumOp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:48.066739+00:00
-- url     : https://prove2.me/submissions/5c3a99a9-91b1-4620-a366-43dc957cd960

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_HasConductorMulShift
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_ExistsFFNeZeroThree
import Theorems.Thm_GlobalTheory_LatPair_sumOp_apply


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix IsLocalRing
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.LatPair GlobalTheory.LatPair.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n n' : Type*}
namespace GlobalTheory.LatPair.Model
theorem _root_.solution (S S' : Pair k n → Finset (Pair k n)) (w w' : Pair k n → Pair k n → ℂ)
    (hS : ∀ P Q, Q ∈ S P ↔ P ∈ S' Q) (hw : ∀ P Q, Q ∈ S P → w P Q = (starRingEnd ℂ) (w' Q P)) :
    IsAdj (sumOp S w) (sumOp S' w') := by
  classical
  intro φ φ' h h'
  unfold cntIp
  rw [finsum_eq_sum_of_support_subset (s := h'.toFinset) _ (fun P hP => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or, map_eq_zero] at hP
      simpa using hP.2),
    finsum_eq_sum_of_support_subset (s := h.toFinset) _ (fun P hP => by
      simp only [Function.mem_support, ne_eq, mul_eq_zero, not_or] at hP
      simpa using hP.1)]
  have e1 : ∀ P, sumOp S w φ P = ∑ Q ∈ h.toFinset, if Q ∈ S P then w P Q * φ Q else 0 := fun P => by
    rw [sumOp_apply, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm
    have : φ Q = 0 := by simpa [hQ] using hQ'
    simp [this]
  have e2 : ∀ Q, sumOp S' w' φ' Q = ∑ P ∈ h'.toFinset, if P ∈ S' Q then w' Q P * φ' P else 0 := fun P => by
    rw [sumOp_apply, ← Finset.sum_filter]
    refine (Finset.sum_subset (fun Q hQ => (Finset.mem_filter.1 hQ).2) fun Q hQ hQ' => ?_).symm
    have : φ' Q = 0 := by simpa [hQ] using hQ'
    simp [this]
  simp only [e1, e2, Finset.sum_mul, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun Q _ => Finset.sum_congr rfl fun P _ => ?_
  by_cases hQ : Q ∈ S P
  · rw [if_pos hQ, if_pos ((hS P Q).1 hQ), hw P Q hQ, map_mul]
    ring
  · rw [if_neg hQ, if_neg (fun h => hQ ((hS P Q).2 h))]
    simp
end GlobalTheory.LatPair.Model
