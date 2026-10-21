-- Prove2me | solution 1 for MazurTransfer.original_continuous_scalar_kernel_characters_injective_covariant_and_locally_vanishing
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T18:39:22.407227+00:00
-- url     : https://prove2.me/submissions/27a34e5b-6151-4db3-8b85-76e7300b4956

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inject the original continuous scalar-character H1 into genuine continuous characters of the same character kernel, retaining its conjugation covariance and vanishing on every supplied local subgroup intersection.
Named downstream consumer: the actual unramified arithmetic character-kernel embedding and its dimension bound.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousScalarKernelCharacterMapsData20261019
import Theorems.Thm_MazurTransfer_original_continuous_scalar_character_kernel_restriction_injective
import Theorems.Thm_MazurTransfer_original_trivial_continuous_cohomology_characters_bijective
noncomputable section
open MazurTransfer ScalarCharacterLine RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
open ContinuousScalarCharacterKernelRestriction ContinuousScalarKernelCharacters
namespace MazurTransfer.ContinuousScalarKernelCharactersProofBoundary20261019
end MazurTransfer.ContinuousScalarKernelCharactersProofBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: inject scalar-character continuous H1 into GENUINE
continuous characters of the SAME character kernel. Preserve conjugation
covariance and vanishing on intersections with each given local subgroup.
Named downstream consumer: actual reflected-character arithmetic Selmer
classes, retaining all genuine valuation inertia conditions.
-/

noncomputable section
namespace MazurTransfer.OriginalContinuousScalarKernelCharactersProof20261019
open MazurTransfer.ContinuousScalarKernelCharacters
open ScalarCharacterLine RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
open ContinuousScalarCharacterKernelRestriction
variable {k G : Type} [Field k] [Group G] [TopologicalSpace G]
variable (χ : G →* kˣ)
local notation "M" => Coefficient (scalarRepresentation χ)



theorem kernelCharacters_injective : Function.Injective (kernelCharacters χ) :=
  (MazurTransfer.original_trivial_continuous_cohomology_characters_bijective.2.2.1 χ.ker M (kernel_action_trivial χ)).comp
    (MazurTransfer.original_continuous_scalar_character_kernel_restriction_injective.2.2.2.2 χ)

theorem kernelCharacters_classMap (z : continuousCocycles G M) (s : χ.ker) :
    ((kernelCharacters χ (classMap G M z)).toMul s).val = cocycleValue χ z s.val := rfl



theorem cocycleValue_one (z : continuousCocycles G M) : cocycleValue χ z 1 = 0 :=
  congrArg (fun x : Additive M => x.toMul.val) (groupCohomology.cocycles₁_map_one z.val)

theorem cocycleValue_conjugate (z : continuousCocycles G M) (g : G) (s : χ.ker) :
    cocycleValue χ z (g * s.val * g⁻¹) = (χ g : k) * cocycleValue χ z s.val := by
  have hi := MazurTransfer.original_continuous_scalar_character_kernel_restriction_injective.1 χ z g g⁻¹
  rw [mul_inv_cancel, cocycleValue_one] at hi
  have hc := MazurTransfer.original_continuous_scalar_character_kernel_restriction_injective.1 χ z (g * s.val) g⁻¹
  rw [MazurTransfer.original_continuous_scalar_character_kernel_restriction_injective.1 χ z g s.val] at hc
  have hs : χ s.val = 1 := s.property
  simp only [map_mul, Units.val_mul, hs, Units.val_one, mul_one] at hc
  calc
    cocycleValue χ z (g * s.val * g⁻¹) =
        (χ g : k) * cocycleValue χ z s.val +
          (cocycleValue χ z g + (χ g : k) * cocycleValue χ z g⁻¹) := by rw [hc]; ring
    _ = (χ g : k) * cocycleValue χ z s.val := by rw [← hi, add_zero]

theorem kernelCharacters_conjugate (x : H1 G M) (g : G) (s : χ.ker) :
    ((kernelCharacters χ x).toMul (conjugateKernelElement χ g s)).val =
      (χ g : k) * ((kernelCharacters χ x).toMul s).val := by
  refine Quotient.inductionOn x ?_
  intro z
  exact cocycleValue_conjugate χ z g s

theorem kernelCharacters_eq_one_of_restriction_zero (x : H1 G M) (T : Subgroup G)
    (hx : restriction G M T x = 0) (s : χ.ker) (hs : s.val ∈ T) :
    (kernelCharacters χ x).toMul s = 1 := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro z hz
  obtain ⟨m, hm⟩ := (restriction_classMap_zero_iff G M T z).mp hz
  apply Coefficient.ext
  change cocycleValue χ z s.val = 0
  have he := congrArg Coefficient.val (hm ⟨s.val, hs⟩)
  change (χ s.val : k) * m.val - m.val = cocycleValue χ z s.val at he
  rw [s.property, Units.val_one, one_mul, sub_self] at he
  exact he.symm

end MazurTransfer.OriginalContinuousScalarKernelCharactersProof20261019

theorem solution : (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ), Function.Injective (kernelCharacters χ)) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ))) (s : χ.ker), ((kernelCharacters χ (classMap G (Coefficient (scalarRepresentation χ)) z)).toMul s).val = cocycleValue χ z s.val) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ))), cocycleValue χ z 1 = 0) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ))) (g : G) (s : χ.ker), cocycleValue χ z (g * s.val * g⁻¹) = (χ g : k) * cocycleValue χ z s.val) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (x : H1 G (Coefficient (scalarRepresentation χ))) (g : G) (s : χ.ker), ((kernelCharacters χ x).toMul (conjugateKernelElement χ g s)).val =
      (χ g : k) * ((kernelCharacters χ x).toMul s).val) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (x : H1 G (Coefficient (scalarRepresentation χ))) (T : Subgroup G)
    (hx : restriction G (Coefficient (scalarRepresentation χ)) T x = 0) (s : χ.ker) (hs : s.val ∈ T), (kernelCharacters χ x).toMul s = 1) := by
  exact ⟨MazurTransfer.OriginalContinuousScalarKernelCharactersProof20261019.kernelCharacters_injective, MazurTransfer.OriginalContinuousScalarKernelCharactersProof20261019.kernelCharacters_classMap, MazurTransfer.OriginalContinuousScalarKernelCharactersProof20261019.cocycleValue_one, MazurTransfer.OriginalContinuousScalarKernelCharactersProof20261019.cocycleValue_conjugate, MazurTransfer.OriginalContinuousScalarKernelCharactersProof20261019.kernelCharacters_conjugate, MazurTransfer.OriginalContinuousScalarKernelCharactersProof20261019.kernelCharacters_eq_one_of_restriction_zero⟩
#print axioms solution
