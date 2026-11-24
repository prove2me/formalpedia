-- Prove2me | solution 1 for GlobalTheory.TameKummer.exists_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:27:35.242005+00:00
-- url     : https://prove2.me/submissions/0a38fafe-07af-4486-8e38-e1b5c19442df

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Theorems.Thm_GlobalTheory_GaloisPowerRoots_exists_pow_finrank_eq


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
theorem _root_.solution {R : Type} (K : Type*) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    (L : Type) [Field L] [Algebra K L] [FiniteDimensional K L] [Algebra.IsSeparable K L]
    (hn : IsUnit ((Module.finrank K L : ℕ) : R)) :
    ∃ ρ : L, ρ ^ Module.finrank K L = algebraMap K L (algebraMap R K π) := by
  first
  | exact @_root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq
  | exact _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq
  | (apply _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq <;> assumption)
  | (intros; apply _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.GaloisPowerRoots.exists_pow_finrank_eq ..)
end GlobalTheory.TameKummer
