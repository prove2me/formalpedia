-- Prove2me | solution 1 for GlobalTheory.TameKummer.exists_generator
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:15:36.357097+00:00
-- url     : https://prove2.me/submissions/7945a0f3-ad2a-4e41-ad1e-7aaf81d50ed9

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
import Theorems.Thm_GlobalTheory_TameKummer_minpoly_eq
import Theorems.Thm_GlobalTheory_TameKummer_mem_range_of_pow_eq_one
import Theorems.Thm_GlobalTheory_TameKummer_isClosed_eval

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
    [IsDiscreteValuationRing R] (hH : HenselianLocalRing R) [IsAlgClosed (ResidueField R)]
    [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] {π : R} (hπ : Irreducible π)
    {l : ℕ} (hl : IsUnit (l : R)) (Ω : Type*) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] :
    ∃ σ : Ω ≃ₐ[K] Ω, ∀ (m : ℕ) (ρ : Ω), ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) →
      ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : IsGalois K Ω := {}
  have hl0 : l ≠ 0 := by
    rintro rfl
    simp at hl
  have hlm : ∀ m, IsUnit ((l ^ m : ℕ) : R) := fun m => by simpa using hl.pow m
  have hπ0 : algebraMap K Ω (algebraMap R K π) ≠ 0 := by
    simpa using hπ.ne_zero
  let G : ℕ → Set (Ω ≃ₐ[K] Ω) := fun m => {σ | ∀ ρ : Ω,
    ρ ^ l ^ m = algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ σ ρ = ζ * ρ}
  have hcl : ∀ m, IsClosed (G m) := fun m => by
    have : G m = ⋂ ρ : Ω, {σ : Ω ≃ₐ[K] Ω | σ ρ ∈ {y | ρ ^ l ^ m =
        algebraMap K Ω (algebraMap R K π) → ∃ ζ, IsPrimitiveRoot ζ (l ^ m) ∧ y = ζ * ρ}} := by
      ext σ
      simp [G]
    rw [this]
    exact isClosed_iInter fun ρ => isClosed_eval ρ _
  have hdec : ∀ m, G (m + 1) ⊆ G m := fun m σ hσ ρ hρ => by
    obtain ⟨ρ', rfl⟩ := IsAlgClosed.exists_pow_nat_eq ρ (Nat.pos_of_ne_zero hl0)
    obtain ⟨ζ, hζ, h⟩ := hσ ρ' (by rw [← hρ, ← pow_mul, pow_succ'])
    refine ⟨ζ ^ l, hζ.pow (Nat.pos_of_ne_zero (pow_ne_zero _ hl0)) (pow_succ' _ _), ?_⟩
    rw [map_pow, h, mul_pow]
  have hne : ∀ m, (G m).Nonempty := fun m => by
    have hn : l ^ m ≠ 0 := pow_ne_zero _ hl0
    obtain ⟨ρ₀, hρ₀⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap K Ω (algebraMap R K π))
      (Nat.pos_of_ne_zero hn)
    have h0 : ρ₀ ≠ 0 := by
      rintro rfl
      exact hπ0 (by rw [← hρ₀, zero_pow hn])
    obtain ⟨v, hv⟩ := exists_isPrimitiveRoot (hlm m)
    have hζ := (hv.map_of_injective (f := algebraMap R K)
      (IsFractionRing.injective R K)).map_of_injective
      (f := algebraMap K Ω) (algebraMap K Ω).injective
    set ζ := algebraMap K Ω (algebraMap R K v)
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root' (x := ζ * ρ₀) (y := ρ₀) (K := K)
      (Algebra.IsAlgebraic.isAlgebraic _)
      (by rw [minpoly_eq K hπ hn hρ₀]; simp [mul_pow, hζ.pow_eq_one, hρ₀])
    refine ⟨σ, fun ρ hρ => ⟨ζ, hζ, ?_⟩⟩
    obtain ⟨η, hη⟩ := mem_range_of_pow_eq_one K (hlm m) (ζ := ρ / ρ₀)
      (by rw [div_pow, hρ, hρ₀, div_self hπ0])
    have : ρ = algebraMap K Ω η * ρ₀ := by rw [hη, div_mul_cancel₀ _ h0]
    rw [this, map_mul, AlgEquiv.commutes, hσ]
    ring
  obtain ⟨σ, hσ⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed G hdec hne
    (hcl 0).isCompact hcl
  exact ⟨σ, fun m => Set.mem_iInter.1 hσ m⟩
end GlobalTheory.TameKummer
