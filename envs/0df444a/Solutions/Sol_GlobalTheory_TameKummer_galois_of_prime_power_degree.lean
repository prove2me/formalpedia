-- Prove2me | solution 1 for GlobalTheory.TameKummer.galois_of_prime_power_degree
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:34:15.551147+00:00
-- url     : https://prove2.me/submissions/59c19810-ee55-4c37-9e24-bd5402153cbe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_GaloisOfPrimePowerDegree
import Theorems.Thm_GlobalTheory_TameKummer_mem_range_of_pow_eq_one
import Theorems.Thm_GlobalTheory_TameKummer_exists_generator
import Theorems.Thm_GlobalTheory_TameKummer_le_adjoin_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
namespace GlobalTheory.TameKummer
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [Field K] [CharZero K] [Algebra R K], SH R K → ∀ (π : R), Irreducible π → ∀ (l : ℕ), l.Prime → IsUnit (l : R) → ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω], (∀ L : IntermediateField K Ω, FiniteDimensional K L → Normal K L → IsPGroup l (L ≃ₐ[K] L) → ∃ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) ∧ L ≤ IntermediateField.adjoin K {ρ}) ∧ (∀ (m : ℕ) (ζ : Ω), ζ ^ l ^ m = 1 → ζ ∈ Set.range (algebraMap K Ω)) ∧ ∃ σ : Ω ≃ₐ[K] Ω, ∀ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ := by
  rintro R K _ _ _ _ _ _ ⟨h1, h2, h3, h4⟩ π hπ l hl hu Ω _ _ _
  obtain rfl : ‹IsLocalRing R› = h2.toIsLocalRing := rfl
  refine ⟨fun L hL hN hp => ?_, fun m ζ hζ => ?_, GlobalTheory.TameKummer.exists_generator K h2 hπ hu Ω⟩
  · have : IsGalois K L := {}
    have : Fact l.Prime := ⟨hl⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hp
    rw [IsGalois.card_aut_eq_finrank] at hm
    obtain ⟨ρ, h⟩ := GlobalTheory.TameKummer.le_adjoin_root K h2 hπ L (by rw [hm]; simpa using hu.pow m)
    exact ⟨m, ρ, hm ▸ h⟩
  · exact GlobalTheory.TameKummer.mem_range_of_pow_eq_one (R := R) K (by simpa using hu.pow m) hζ
end GlobalTheory.TameKummer
