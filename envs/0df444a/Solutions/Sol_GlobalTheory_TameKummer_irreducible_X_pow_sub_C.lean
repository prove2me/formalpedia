-- Prove2me | solution 1 for GlobalTheory.TameKummer.irreducible_X_pow_sub_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:36.980921+00:00
-- url     : https://prove2.me/submissions/b08342a3-f6de-4599-bfe0-2b15247fcbb3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.TameKummer
open IsLocalRing Polynomial
namespace GlobalTheory.TameKummer
theorem _root_.solution {R : Type*} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K] {π : R}
    (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) :
    Irreducible (X ^ n - C (algebraMap R K π) : K[X]) := by
  have hm := monic_X_pow_sub_C π hn
  have h : Irreducible (X ^ n - C π : R[X]) := by
    refine irreducible_of_eisenstein_criterion (P := Ideal.span {π})
      ((Ideal.span_singleton_prime hπ.ne_zero).2 hπ.prime) ?_ ?_ ?_ ?_ hm.isPrimitive
    · rw [hm.leadingCoeff, Ideal.mem_span_singleton]
      exact fun h => hπ.not_isUnit (isUnit_of_dvd_one h)
    · intro i hi
      rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn), Nat.cast_lt] at hi
      rw [coeff_sub, coeff_X_pow, if_neg hi.ne, coeff_C, Ideal.mem_span_singleton]
      split_ifs <;> simp
    · rw [degree_X_pow_sub_C (Nat.pos_of_ne_zero hn)]
      exact_mod_cast Nat.pos_of_ne_zero hn
    · rw [coeff_sub, coeff_X_pow, if_neg hn.symm, coeff_C, if_pos rfl, Ideal.span_singleton_pow,
        Ideal.mem_span_singleton, zero_sub, dvd_neg]
      intro h
      have : π * π ∣ π * 1 := by simpa [sq] using h
      exact hπ.not_isUnit (isUnit_of_dvd_one ((mul_dvd_mul_iff_left hπ.ne_zero).1 this))
  simpa using (hm.irreducible_iff_irreducible_map_fraction_map (K := K)).1 h
end GlobalTheory.TameKummer
