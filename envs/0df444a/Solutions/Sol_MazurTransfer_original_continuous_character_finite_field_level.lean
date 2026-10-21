-- Prove2me | solution 1 for MazurTransfer.original_continuous_character_finite_field_level
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T21:08:03.333175+00:00
-- url     : https://prove2.me/submissions/92d78d4f-8d81-44cc-bf80-72a54efa1b45

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a genuine continuous character on the same open absolute Galois subgroup vanishes on the fixing subgroup of an actual finite intermediate field. Preserve all original hypotheses.
Named downstream consumer: the actual selected reflected-character finite-level input to the official uniform-character theorem.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousCharacterFiniteFieldLevelData20261019
noncomputable section
open MazurTransfer.ContinuousCharacterFiniteFieldLevel
namespace MazurTransfer.OriginalContinuousCharacterFiniteFieldLevelProofBoundary20261019
end MazurTransfer.OriginalContinuousCharacterFiniteFieldLevelProofBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: a genuine continuous character on a GIVEN open Galois
subgroup, with discrete coefficients, vanishes on the fixing subgroup of
an ACTUAL finite intermediate field. Use its literal open kernel.
Named downstream consumer: the finite-level input of the checked official
uniform-character theorem for the actual degree-six reflected field.
-/

noncomputable section
namespace MazurTransfer.ContinuousCharacterFiniteFieldLevel
variable (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K]
  [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M]
local notation "Γ" => K ≃ₐ[ℚ] K



theorem characterKernel_isOpen (S : Subgroup Γ) (f : S →ₜ* M) (hS : IsOpen (S : Set Γ)) :
    IsOpen (characterKernel K M S f : Set Γ) := by
  have hk : IsOpen (f.toMonoidHom.ker : Set S) :=
    (isOpen_discrete ({1} : Set M)).preimage f.continuous
  exact hS.isOpenMap_subtype_val _ hk



theorem characterField_fixingSubgroup (S : Subgroup Γ) (f : S →ₜ* M) (hS : IsOpen (S : Set Γ)) :
    (characterField K M S f).fixingSubgroup = characterKernel K M S f :=
  InfiniteGalois.fixingSubgroup_fixedField
    ⟨characterKernel K M S f, (characterKernel K M S f).isClosed_of_isOpen (characterKernel_isOpen K M S f hS)⟩

theorem characterField_finiteDimensional (S : Subgroup Γ) (f : S →ₜ* M) (hS : IsOpen (S : Set Γ)) :
    FiniteDimensional ℚ (characterField K M S f) := by
  apply (InfiniteGalois.isOpen_iff_finite (characterField K M S f)).mp
  rw [characterField_fixingSubgroup K M S f hS]
  exact characterKernel_isOpen K M S f hS

theorem exists_finite_field_level (S : Subgroup Γ) (f : S →ₜ* M) (hS : IsOpen (S : Set Γ)) :
    ∃ L : IntermediateField ℚ K, FiniteDimensional ℚ L ∧
      ∀ σ ∈ L.fixingSubgroup, ∃ hσ : σ ∈ S, f ⟨σ, hσ⟩ = 1 := by
  refine ⟨characterField K M S f, characterField_finiteDimensional K M S f hS, ?_⟩
  intro σ hσ
  have hm : σ ∈ characterKernel K M S f := (le_of_eq (characterField_fixingSubgroup K M S f hS)) hσ
  obtain ⟨s, hs, he⟩ := hm
  subst σ
  exact ⟨s.property, hs⟩

end MazurTransfer.ContinuousCharacterFiniteFieldLevel

theorem solution : (∀ (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K] [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M] (S : Subgroup (K ≃ₐ[ℚ] K)) (f : S →ₜ* M) (hS : IsOpen (S : Set (K ≃ₐ[ℚ] K))), IsOpen (characterKernel K M S f : Set (K ≃ₐ[ℚ] K))) ∧ (∀ (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K] [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M] (S : Subgroup (K ≃ₐ[ℚ] K)) (f : S →ₜ* M) (hS : IsOpen (S : Set (K ≃ₐ[ℚ] K))), (characterField K M S f).fixingSubgroup = characterKernel K M S f) ∧ (∀ (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K] [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M] (S : Subgroup (K ≃ₐ[ℚ] K)) (f : S →ₜ* M) (hS : IsOpen (S : Set (K ≃ₐ[ℚ] K))), FiniteDimensional ℚ (characterField K M S f)) ∧ (∀ (K M : Type) [Field K] [CharZero K] [IsGalois ℚ K] [CommGroup M] [TopologicalSpace M] [IsTopologicalGroup M] [DiscreteTopology M] (S : Subgroup (K ≃ₐ[ℚ] K)) (f : S →ₜ* M) (hS : IsOpen (S : Set (K ≃ₐ[ℚ] K))), ∃ L : IntermediateField ℚ K, FiniteDimensional ℚ L ∧ ∀ σ ∈ L.fixingSubgroup, ∃ hσ : σ ∈ S, f ⟨σ, hσ⟩ = 1) := by
  exact ⟨MazurTransfer.ContinuousCharacterFiniteFieldLevel.characterKernel_isOpen, MazurTransfer.ContinuousCharacterFiniteFieldLevel.characterField_fixingSubgroup, MazurTransfer.ContinuousCharacterFiniteFieldLevel.characterField_finiteDimensional, MazurTransfer.ContinuousCharacterFiniteFieldLevel.exists_finite_field_level⟩
#print axioms solution
