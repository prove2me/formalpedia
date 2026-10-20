-- Prove2me | solution 1 for MazurTransfer.original_submodule_character_image_finite_dimension_and_finrank_bound
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-19T13:27:43.343887+00:00
-- url     : https://prove2.me/submissions/1245b838-a591-471e-b7d6-b69fba0612b4

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: bound a given source subspace by the given finite-dimensional quotient image and a given finite-dimensional character subspace covering its kernel. Both finiteness hypotheses are retained as inputs.
Named downstream consumer: the actual pi norm Kummer image bound from its same selected quotient and unramified character submodule.
-/
import Definitions.Def_MazurTransfer_OriginalSubmoduleCharacterImageDimensionBoundData20261019
noncomputable section
open MazurTransfer SubmoduleCharacterImageDimensionBound
namespace MazurTransfer.CharacterImageDimensionProofBoundary20261019
end MazurTransfer.CharacterImageDimensionProofBoundary20261019
noncomputable section
namespace MazurTransfer.OriginalCharacterImageDimensionProof20261019
open MazurTransfer.SubmoduleCharacterImageDimensionBound
variable {k A V W : Type} [Field k]
  [AddCommGroup A] [Module k A] [AddCommGroup V] [Module k V]
  [AddCommGroup W] [Module k W]





theorem characterKernelMap_injective (E : Submodule k V) (f : V →ₗ[k] W) (i : A →ₗ[k] V)
    (C : Submodule k A) (hker : ∀ x : E, f x.val = 0 → x.val ∈ C.map i) :
    Function.Injective (characterKernelMap E f i C hker) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun z : C.map i => (z : V)) h

theorem source_finite_and_finrank_bound
    (E : Submodule k V) (f : V →ₗ[k] W) (i : A →ₗ[k] V)
    (C : Submodule k A) (D : Submodule k W)
    [FiniteDimensional k C] [FiniteDimensional k D]
    (himage : LinearMap.range (restrictedQuotient E f) ≤ D)
    (hker : ∀ x : E, f x.val = 0 → x.val ∈ C.map i) :
    FiniteDimensional k E ∧ Module.finrank k E ≤ Module.finrank k C + Module.finrank k D := by
  let g := restrictedQuotient E f
  haveI : FiniteDimensional k (C.map i) := inferInstance
  haveI : FiniteDimensional k g.ker :=
    FiniteDimensional.of_injective (characterKernelMap E f i C hker)
      (characterKernelMap_injective E f i C hker)
  haveI : FiniteDimensional k g.range :=
    FiniteDimensional.of_injective (Submodule.inclusion himage) (Submodule.inclusion_injective himage)
  have htop : Submodule.comap g g.range = ⊤ := by
    ext x
    exact iff_of_true ⟨x, rfl⟩ (Submodule.mem_top)
  haveI : FiniteDimensional k (⊤ : Submodule k E) := by
    rw [← htop]
    infer_instance
  have hE : FiniteDimensional k E := Module.Finite.of_surjective
    (⊤ : Submodule k E).subtype (fun x => ⟨⟨x, Submodule.mem_top⟩, rfl⟩)
  letI := hE
  have hk : Module.finrank k g.ker ≤ Module.finrank k C :=
    ((characterKernelMap E f i C hker).finrank_le_finrank_of_injective
      (characterKernelMap_injective E f i C hker)).trans (Submodule.finrank_map_le _ _)
  have hd : Module.finrank k g.range ≤ Module.finrank k D :=
    (Submodule.inclusion himage).finrank_le_finrank_of_injective (Submodule.inclusion_injective himage)
  exact ⟨hE, by have h := g.finrank_range_add_finrank_ker; omega⟩

end MazurTransfer.OriginalCharacterImageDimensionProof20261019

theorem solution : (∀ {k A V W : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (E : Submodule k V) (f : V →ₗ[k] W) (i : A →ₗ[k] V)
    (C : Submodule k A) (hker : ∀ x : E, f x.val = 0 → x.val ∈ C.map i), Function.Injective (characterKernelMap E f i C hker)) ∧ (∀ {k A V W : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W] (E : Submodule k V) (f : V →ₗ[k] W) (i : A →ₗ[k] V)
    (C : Submodule k A) (D : Submodule k W)
    [FiniteDimensional k C] [FiniteDimensional k D]
    (himage : LinearMap.range (restrictedQuotient E f) ≤ D)
    (hker : ∀ x : E, f x.val = 0 → x.val ∈ C.map i), FiniteDimensional k E ∧ Module.finrank k E ≤ Module.finrank k C + Module.finrank k D) := by
  exact ⟨MazurTransfer.OriginalCharacterImageDimensionProof20261019.characterKernelMap_injective, MazurTransfer.OriginalCharacterImageDimensionProof20261019.source_finite_and_finrank_bound⟩
#print axioms solution
