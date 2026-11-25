-- Prove2me | solution 1 for GlobalTheory.IntFiniteTypeDim.exists_natPrime_mem_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:17:40.984044+00:00
-- url     : https://prove2.me/submissions/71872731-b025-4753-99ec-3cfcb66e276e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KrullDimQuotientMinimalPrimeOverL
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RingKrullDimQuotientLeOfMinimalPrimes
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_isJacobsonRing_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntFiniteTypeDim
namespace GlobalTheory.IntFiniteTypeDim
theorem _root_.solution (A : Type) [CommRing A] [Algebra.FiniteType ℤ A]
    (m : Ideal A) [m.IsMaximal] : ∃ l : ℕ, l.Prime ∧ (l : A) ∈ m := by
  haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  letI := Ideal.Quotient.field m
  have hfin : Module.Finite ℤ (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ m)
  obtain ⟨p, hp⟩ := CharP.exists (A ⧸ m)
  rcases CharP.char_is_prime_or_zero (A ⧸ m) p with h | h
  · refine ⟨p, h, ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ p
  · subst h
    haveI : CharZero (A ⧸ m) := CharP.charP_to_charZero _
    exfalso
    have hinj : Function.Injective (algebraMap ℤ (A ⧸ m)) :=
      RingHom.injective_int _
    exact Int.not_isField
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (A ⧸ m)))
end GlobalTheory.IntFiniteTypeDim
