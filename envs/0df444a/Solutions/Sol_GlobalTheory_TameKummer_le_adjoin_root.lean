-- Prove2me | solution 1 for GlobalTheory.TameKummer.le_adjoin_root
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:57:05.22485+00:00
-- url     : https://prove2.me/submissions/67b0cc13-0a52-4ab3-b199-266cf8849579

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Theorems.Thm_GlobalTheory_TameKummer_minpoly_eq
import Theorems.Thm_GlobalTheory_TameKummer_exists_root

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
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    {Ω : Type} [Field Ω] [Algebra K Ω] (L : IntermediateField K Ω) [FiniteDimensional K L]
    (hn : IsUnit ((Module.finrank K L : ℕ) : R)) :
    ∃ ρ : Ω, ρ ^ Module.finrank K L = algebraMap K Ω (algebraMap R K π) ∧
      L ≤ IntermediateField.adjoin K {ρ} := by
  obtain ⟨ρ, hρ⟩ := exists_root K hH hπ L hn
  have hn0 : Module.finrank K L ≠ 0 := Module.finrank_pos.ne'
  have hρ' : (ρ : Ω) ^ Module.finrank K L = algebraMap K Ω (algebraMap R K π) := by
    have := congrArg (algebraMap L Ω) hρ
    rwa [map_pow, ← IsScalarTower.algebraMap_apply] at this
  refine ⟨ρ, hρ', ge_of_eq (IntermediateField.eq_of_le_of_finrank_eq ?_ ?_)⟩
  · simp
  · have hi : IsIntegral K (ρ : Ω) := (Algebra.IsIntegral.isIntegral (R := K) ρ).map L.val
    rw [IntermediateField.adjoin.finrank hi, minpoly_eq K hπ hn0 hρ', natDegree_X_pow_sub_C]
end GlobalTheory.TameKummer
