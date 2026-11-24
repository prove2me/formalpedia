-- Prove2me | solution 1 for GlobalTheory.TameKummer.mem_range_of_pow_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:53:28.04477+00:00
-- url     : https://prove2.me/submissions/378bd5f6-96b1-458c-ac93-c83b1f39af8f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Theorems.Thm_GlobalTheory_TameKummer_exists_isPrimitiveRoot

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
theorem _root_.solution {R : Type*} (K : Type*) [CommRing R] [HenselianLocalRing R]
    [IsAlgClosed (ResidueField R)] [Field K] [Algebra R K] [IsFractionRing R K] {n : ℕ}
    (hn : IsUnit (n : R)) {Ω : Type*} [Field Ω] [Algebra K Ω] {ζ : Ω} (hζ : ζ ^ n = 1) :
    ζ ∈ Set.range (algebraMap K Ω) := by
  have : NeZero n := ⟨by
    rintro rfl
    simp at hn⟩
  obtain ⟨v, hv⟩ := exists_isPrimitiveRoot hn
  have h := (hv.map_of_injective (f := algebraMap R K) (IsFractionRing.injective R K)).map_of_injective
    (f := algebraMap K Ω) (algebraMap K Ω).injective
  obtain ⟨i, -, rfl⟩ := h.eq_pow_of_pow_eq_one hζ
  exact ⟨_, map_pow _ _ _⟩
end GlobalTheory.TameKummer
