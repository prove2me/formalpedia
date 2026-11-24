-- Prove2me | solution 1 for GlobalTheory.HermClass.exists_int_mul_mem_span
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:27:49.687627+00:00
-- url     : https://prove2.me/submissions/5140a41c-2caa-4dbd-9968-e751f336f66d

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsShortOfTraceDet_f72bcdc76e7ca34f
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AdelicLattices__ExistsIntMulIsIntegralOfTrace_d66162b46f1d0309

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
    ∃ M : ℤ, M ≠ 0 ∧ ∀ J : Ideal (𝓞 E), J ≠ ⊥ →
      ∃ j ∈ J, j ≠ 0 ∧ ∀ a ∈ J, j ∣ (M : 𝓞 E) * a := by
  classical
  choose I hI using ClassGroup.mk0_surjective (R := 𝓞 E)
  refine ⟨∏ C, (Ideal.absNorm (I C : Ideal (𝓞 E)) : ℤ), Finset.prod_ne_zero_iff.2 fun C _ => ?_,
    fun J hJ => ?_⟩
  · exact_mod_cast Ideal.absNorm_ne_zero_of_nonZeroDivisors (I C)
  · let J' : nonZeroDivisors (Ideal (𝓞 E)) := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
    obtain ⟨j, hj0, hj⟩ := ClassGroup.mk0_eq_mk0_inv_iff.1 (hI (ClassGroup.mk0 J')⁻¹)
    refine ⟨j, ?_, hj0, fun a ha => ?_⟩
    · have hjm : j ∈ (I (ClassGroup.mk0 J')⁻¹ : Ideal (𝓞 E)) * J := by
        rw [hj]; exact Ideal.mem_span_singleton_self j
      exact (Ideal.mul_le_inf hjm).2
    · have hj' : (I (ClassGroup.mk0 J')⁻¹ : Ideal (𝓞 E)) * J = Ideal.span {j} := hj
      rw [← Ideal.mem_span_singleton, ← hj']
      refine Ideal.mul_mem_mul ?_ ha
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ (ClassGroup.mk0 J')⁻¹), Int.cast_mul]
      refine Ideal.mul_mem_right _ _ ?_
      simpa using Ideal.absNorm_mem _
end GlobalTheory.HermClass
