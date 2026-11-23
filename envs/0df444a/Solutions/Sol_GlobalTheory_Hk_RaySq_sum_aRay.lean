-- Prove2me | solution 1 for GlobalTheory.Hk.RaySq.sum_aRay
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:58.648656+00:00
-- url     : https://prove2.me/submissions/8d67ee9a-d60f-4baa-90b9-3c2b103fed35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ConvRealChar
import Theorems.Thm_GlobalTheory_Hk_RaySq_mem_normEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RaySq
variable {K : Type} [Field K] [NumberField K]
variable {M : ℕ} (D : RayData K M)
namespace GlobalTheory.Hk.RaySq
theorem _root_.solution (ε : D.G → ℝ) (n : ℕ) : ∑ g, ε g * aRay D g n = ∑ I ∈ normEq K n, chi D ε I := by
  have hcard : ∀ g, aRay D g n = (((normEq K n).filter (fun I =>
      (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g)).card : ℝ) := by
    intro g
    unfold aRay
    congr 1
    rw [← Set.ncard_coe_finset]
    congr 1
    ext I
    simp only [idealsIn, Finset.coe_filter, Set.mem_setOf_eq, mem_normEq]
    tauto
  have hchi : ∀ I, chi D ε I = ∑ g, if (I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})) ∧ D.cls I = g
      then ε g else 0 := by
    intro I
    by_cases h : I ≠ ⊥ ∧ IsCoprime I (Ideal.span {(M : 𝓞 K)})
    · rw [chi, if_pos h]
      simp only [ite_and, if_pos h]
      simp
    · rw [chi, if_neg h]
      simp only [ite_and, if_neg h, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl (fun I _ => hchi I), Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, hcard g, mul_comm]
end GlobalTheory.Hk.RaySq
