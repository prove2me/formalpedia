-- Prove2me | solution 1 for GlobalTheory.TameKummer.minpoly_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T21:40:58.123865+00:00
-- url     : https://prove2.me/submissions/fe005d77-799d-4dd7-af1c-dbb0abf67f77

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Theorems.Thm_GlobalTheory_TameKummer_irreducible_X_pow_sub_C

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
    (hπ : Irreducible π) {n : ℕ} (hn : n ≠ 0) {L : Type*} [Field L] [Algebra K L] {ρ : L}
    (hρ : ρ ^ n = algebraMap K L (algebraMap R K π)) :
    minpoly K ρ = X ^ n - C (algebraMap R K π) :=
  (minpoly.eq_of_irreducible_of_monic (irreducible_X_pow_sub_C K hπ hn) (by simp [hρ])
    (monic_X_pow_sub_C _ hn)).symm
end GlobalTheory.TameKummer
