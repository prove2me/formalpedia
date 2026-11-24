-- Prove2me | solution 1 for GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:29:51.32096+00:00
-- url     : https://prove2.me/submissions/0537f665-fbb5-4b11-896d-8b14bab9a988

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ProdClassGroupMk0EqOfLinearEquivPi
import Theorems.Thm_GlobalTheory_DetClass_exists_span_mul_eq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open GlobalTheory.DetClass
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] [IsDedekindDomain R]
    (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰)
    (h : Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R)))) :
    ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) := by
  classical
  obtain ⟨φ⟩ := h
  have hne : ∀ K : (Ideal R)⁰, ∃ e : R, e ∈ (K : Ideal R) ∧ e ≠ 0 := fun K =>
    Submodule.exists_mem_ne_zero_of_ne_bot (nonZeroDivisors.coe_ne_zero K)
  choose e he he0 using hne
  set c : R := (∏ i, e (I i)) * ∏ i, e (J i) with hc
  have hc0 : c ≠ 0 := mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun i _ => he0 _)
    (Finset.prod_ne_zero_iff.mpr fun i _ => he0 _)
  have hI : ∀ i, c ∈ (I i : Ideal R) := fun i =>
    Ideal.mul_mem_right _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (he _))
  have hJ : ∀ i, c ∈ (J i : Ideal R) := fun i =>
    Ideal.mul_mem_left _ _ (Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) (he _))
  obtain ⟨x, y, hx, hy, hxy⟩ := exists_span_mul_eq φ c hc0 hI hJ
  rw [← map_prod, ← map_prod, ClassGroup.mk0_eq_mk0_iff]
  refine ⟨x, y, hx, hy, ?_⟩
  simpa only [Submonoid.coe_finsetProd] using hxy
end GlobalTheory
