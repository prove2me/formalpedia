-- Prove2me | solution 1 for GlobalTheory.exists_intCast_mem_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T22:42:41.543351+00:00
-- url     : https://prove2.me/submissions/c995bf94-fbf5-4231-afb7-bc3cd3c9d62a

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IntToRatA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringLiftOfSpecialFibre
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_RingKrullDimQuotientEqOfMemMinimalPrimes
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsHorizontalPrimeLeOfIsMaximal
import Theorems.Thm_ReciprocityTheory_AnForm_R_IntegerToRational_isJacobsonRing_int


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type*) [CommRing R] [Algebra.FiniteType ℤ R]
    (m : Ideal R) [m.IsMaximal] : ∃ p : ℤ, p ≠ 0 ∧ algebraMap ℤ R p ∈ m := by
  let := Ideal.Quotient.field m
  have := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
  have : Module.Finite ℤ (R ⧸ m) := finite_of_finite_type_of_isJacobsonRing ℤ _
  by_contra h
  push Not at h
  have hinj : Function.Injective (algebraMap ℤ (R ⧸ m)) := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra ha0
    apply h a ha0
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    simpa using ha
  have hF : IsField ℤ :=
    (Algebra.IsIntegral.isField_iff_isField hinj).mpr (Field.toIsField (R ⧸ m))
  exact Int.not_isField hF
end GlobalTheory
