-- Prove2me | solution 1 for GlobalTheory.NonUnitShift.linearIndependent_resolvent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:28:05.412164+00:00
-- url     : https://prove2.me/submissions/a4115c77-028b-4671-bc2a-cb599e8c29f1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_LinearIndependentResolvent
import Theorems.Thm_GlobalTheory_NonUnitShift_isUnit_aeval

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.NonUnitShift
open Polynomial
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace GlobalTheory.NonUnitShift
theorem _root_.solution (T : Module.End ℂ V)
    (h : ∀ c : ℂ, IsUnit (T - algebraMap ℂ (Module.End ℂ V) c)) (v : V) (hv : v ≠ 0)
    (w : ℂ → V) (hw : ∀ c, (T - algebraMap ℂ (Module.End ℂ V) c) (w c) = v) :
    LinearIndependent ℂ w := by
  classical
  rw [linearIndependent_iff']
  intro s g hs i hi
  set q : ℂ[X] := ∑ j ∈ s, C (g j) * ∏ k ∈ s.erase j, (X - C k) with hq
  have key : aeval T q v = 0 := by
    have h1 : aeval T (∏ k ∈ s, (X - C k)) (∑ j ∈ s, g j • w j) = 0 := by
      rw [hs, map_zero]
    rw [← h1, hq, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [← Finset.prod_erase_mul s _ hj, map_mul, map_mul, aeval_C, map_sub, aeval_X, aeval_C,
      map_smul, Module.End.mul_apply, Module.End.mul_apply, hw, Module.algebraMap_end_apply]
  have hq0 : q = 0 := by
    by_contra hne
    have hu := isUnit_aeval T h _ q rfl hne
    have hinj := ((Module.End.isUnit_iff _).1 hu).1
    exact hv (hinj (by rw [key, map_zero]))
  have h2 : eval i q = g i * ∏ k ∈ s.erase i, (i - k) := by
    rw [hq, eval_finsetSum, Finset.sum_eq_single i]
    · simp [eval_prod]
    · intro j _ hji
      rw [eval_mul, eval_prod, Finset.prod_eq_zero (i := i) (Finset.mem_erase.2 ⟨hji.symm, hi⟩) (by simp),
        mul_zero]
    · intro h3
      exact absurd hi h3
  rw [hq0, eval_zero] at h2
  rcases mul_eq_zero.1 h2.symm with h3 | h3
  · exact h3
  · obtain ⟨k, hk, hk0⟩ := Finset.prod_eq_zero_iff.1 h3
    exact absurd (sub_eq_zero.1 hk0).symm (Finset.mem_erase.1 hk).1
end GlobalTheory.NonUnitShift
