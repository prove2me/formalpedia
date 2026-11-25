-- Prove2me | solution 1 for GroundTheory.Arith.Toric.mem_range_of_forall_height_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:54:25.97623+00:00
-- url     : https://prove2.me/submissions/3d0c5dfd-794d-4c56-9812-297b379231bc

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_ToricVarieties_KrullDomain
import Theorems.Thm_GroundTheory_Arith_Toric_smul_mk_eq_zero_iff
import Theorems.Thm_GroundTheory_Arith_Toric_height_eq_one_of_isAssociatedPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Toric
variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
namespace GroundTheory.Arith.Toric
theorem _root_.solution {K : Type*} [Field K] [Algebra A K] [IsFractionRing A K]
    (x : K) (h : ∀ p : Ideal A, p.IsPrime → p.height = 1 →
      ∃ a s : A, s ∉ p ∧ x * algebraMap A K s = algebraMap A K a) :
    x ∈ (algebraMap A K).range := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  have hbK : algebraMap A K b ≠ 0 := fun h => hb0 (hinj (by rw [h, map_zero]))
  by_cases hab : b ∣ a
  · obtain ⟨c, rfl⟩ := hab
    exact ⟨c, by rw [map_mul, mul_div_cancel_left₀ _ hbK]⟩
  · exfalso
    have hne : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
      rw [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
      exact hab
    obtain ⟨P, hP, hcol⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hne
    obtain ⟨a', s, hs, hx⟩ := h P hP.isPrime (height_eq_one_of_isAssociatedPrime hb0 hP)
    apply hs
    apply hcol
    rw [Submodule.mem_colon_singleton, Submodule.mem_bot, smul_mk_eq_zero_iff, mul_comm]
    refine ⟨a', hinj ?_⟩
    rw [map_mul, map_mul, ← hx, div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hbK]
end GroundTheory.Arith.Toric
