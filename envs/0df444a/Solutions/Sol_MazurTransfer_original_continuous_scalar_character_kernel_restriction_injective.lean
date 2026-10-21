-- Prove2me | solution 1 for MazurTransfer.original_continuous_scalar_character_kernel_restriction_injective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T18:22:01.343074+00:00
-- url     : https://prove2.me/submissions/0df55a48-7b1a-4570-ab99-086c2534c269

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restrict the same continuous scalar-character cohomology to the kernel of that character. The subgroup action is intrinsically trivial and restriction is injective. Every original group, field and topology hypothesis is retained.
Named downstream consumer: genuine continuous characters of the same character kernel and the actual reflected-character arithmetic class bound.
-/
import Definitions.Def_MazurTransfer_OriginalContinuousScalarCharacterKernelRestrictionData20261019
import Theorems.Thm_MazurTransfer_original_scalar_cocycle_character_kernel_detection_and_coboundary
import Theorems.Thm_MazurTransfer_ContinuousFirstCohomologySubgroupRestriction_restriction_classMap_zero_iff
noncomputable section
open MazurTransfer ScalarCharacterLine RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
open ContinuousScalarCharacterKernelRestriction
namespace MazurTransfer.ScalarCharacterKernelRestrictionProofBoundary20261019
end MazurTransfer.ScalarCharacterKernelRestrictionProofBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: restrict the EXISTING continuous scalar-character H1
presentation to the kernel of that SAME character. Restriction is
injective, and this subgroup acts trivially on the given coefficients.
No finite group, finite image, splitting, or arithmetic input is assumed.
Named downstream consumer: the actual chi13 kernel-class arithmetic bound.
-/

noncomputable section
namespace MazurTransfer.OriginalScalarCharacterKernelRestrictionProof20261019
open MazurTransfer.ContinuousScalarCharacterKernelRestriction
open ScalarCharacterLine RepresentationDiscreteCoefficients
open ContinuousFirstCohomologyPresentation ContinuousFirstCohomologySubgroupRestriction
variable {k G : Type} [Field k] [Group G] [TopologicalSpace G]
variable (χ : G →* kˣ)
local notation "M" => Coefficient (scalarRepresentation χ)



theorem cocycleValue_mul (z : continuousCocycles G M) (g h : G) :
    cocycleValue χ z (g * h) = cocycleValue χ z g + (χ g : k) * cocycleValue χ z h := by
  have ht := (groupCohomology.mem_cocycles₁_iff _).mp z.val.property g h
  have he := congrArg (fun x : Additive M => x.toMul.val) ht
  change cocycleValue χ z (g * h) = (χ g : k) * cocycleValue χ z h + cocycleValue χ z g at he
  exact he.trans (add_comm _ _)

theorem kernel_action_trivial (s : χ.ker) (m : M) : s • m = m := by
  apply Coefficient.ext
  change (χ s.val : k) * m.val = m.val
  rw [show χ s.val = 1 from s.property, Units.val_one, one_mul]

theorem cocycleValue_eq_zero_on_kernel_of_restriction_zero (z : continuousCocycles G M)
    (hz : restriction G M χ.ker (classMap G M z) = 0) (g : G) (hg : χ g = 1) :
    cocycleValue χ z g = 0 := by
  obtain ⟨m, hm⟩ := (restriction_classMap_zero_iff G M χ.ker z).mp hz
  have ht := congrArg Coefficient.val (hm ⟨g, hg⟩)
  change (χ g : k) * m.val - m.val = cocycleValue χ z g at ht
  rw [hg, Units.val_one, one_mul, sub_self] at ht
  exact ht.symm

theorem eq_zero_of_restriction_zero (x : H1 G M)
    (hx : restriction G M χ.ker x = 0) : x = 0 := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro z hz
  obtain ⟨a, ha⟩ := MazurTransfer.original_scalar_cocycle_character_kernel_detection_and_coboundary.2.2 χ (cocycleValue χ z)
    (cocycleValue_mul χ z) (cocycleValue_eq_zero_on_kernel_of_restriction_zero χ z hz)
  apply (classMap_eq_zero_iff G M z).mpr
  apply (groupCohomology.coboundariesOfIsMulCoboundary₁
    (f := fun g : G => (Additive.toMul (z.val g) : M)) ?_).property
  refine ⟨⟨a⟩, fun g => ?_⟩
  apply Coefficient.ext
  change (χ g : k) * a - a = cocycleValue χ z g
  exact (ha g).symm

theorem restriction_injective : Function.Injective (restriction G M χ.ker) := by
  intro x y hxy
  apply sub_eq_zero.mp
  apply eq_zero_of_restriction_zero χ
  rw [map_sub, hxy, sub_self]

end MazurTransfer.OriginalScalarCharacterKernelRestrictionProof20261019

theorem solution : (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ))) (g h : G), cocycleValue χ z (g * h) = cocycleValue χ z g + (χ g : k) * cocycleValue χ z h) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (s : χ.ker) (m : (Coefficient (scalarRepresentation χ))), s • m = m) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (z : continuousCocycles G (Coefficient (scalarRepresentation χ)))
    (hz : restriction G (Coefficient (scalarRepresentation χ)) χ.ker (classMap G (Coefficient (scalarRepresentation χ)) z) = 0) (g : G) (hg : χ g = 1), cocycleValue χ z g = 0) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ) (x : H1 G (Coefficient (scalarRepresentation χ)))
    (hx : restriction G (Coefficient (scalarRepresentation χ)) χ.ker x = 0), x = 0) ∧ (∀ {k G : Type} [Field k] [Group G] [TopologicalSpace G] (χ : G →* kˣ), Function.Injective (restriction G (Coefficient (scalarRepresentation χ)) χ.ker)) := by
  exact ⟨MazurTransfer.OriginalScalarCharacterKernelRestrictionProof20261019.cocycleValue_mul, MazurTransfer.OriginalScalarCharacterKernelRestrictionProof20261019.kernel_action_trivial, MazurTransfer.OriginalScalarCharacterKernelRestrictionProof20261019.cocycleValue_eq_zero_on_kernel_of_restriction_zero, MazurTransfer.OriginalScalarCharacterKernelRestrictionProof20261019.eq_zero_of_restriction_zero, MazurTransfer.OriginalScalarCharacterKernelRestrictionProof20261019.restriction_injective⟩
#print axioms solution
