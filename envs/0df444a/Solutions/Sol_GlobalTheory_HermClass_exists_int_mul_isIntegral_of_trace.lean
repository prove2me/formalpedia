-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_int_mul_isIntegral_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:37:41.740334+00:00
-- url     : https://prove2.me/submissions/f63c4cb4-622e-4dbe-9caf-3ce182d3e95a

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309
import Theorems.Thm_GlobalTheory_HermClass_exists_int_mul_isIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HermClass
open Module Submodule NumberField
variable (E : Type) [Field E] [NumberField E]
namespace GlobalTheory.HermClass
theorem _root_.solution :
    ∃ D : ℤ, D ≠ 0 ∧ ∀ a : E, (∀ t : E, IsIntegral ℤ t → ∃ m : ℤ, Algebra.trace ℚ E (a * t) = m) →
      IsIntegral ℤ ((D : E) * a) := by
  classical
  obtain ⟨D, hD, h⟩ := exists_int_mul_isIntegral E (Set.finite_range (integralBasis E).traceDual)
  refine ⟨D, hD, fun a ha => ?_⟩
  rw [← (integralBasis E).traceDual.sum_repr a, Finset.mul_sum]
  refine IsIntegral.sum _ fun i _ => ?_
  obtain ⟨m, hm⟩ := ha (integralBasis E i) (by
    rw [integralBasis_apply]; exact (RingOfIntegers.basis E i).isIntegral_coe)
  rw [Basis.traceDual_repr_apply, Algebra.traceForm_apply, hm, mul_smul_comm, Int.cast_smul_eq_zsmul]
  exact (h _ ⟨i, rfl⟩).smul m
end GlobalTheory.HermClass
