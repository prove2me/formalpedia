-- Prove2me | solution 1 for MazurTransfer.original_trivial_continuous_cohomology_characters_bijective
-- status  : ACCEPTED   (prove)
-- author  : @Vas
-- created : 2026-10-20T18:30:57.315199+00:00
-- url     : https://prove2.me/submissions/7a52e822-9b1f-413b-ac84-b7e54591e7dd

/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: for the same supplied trivial action, the original continuous H1 character map is bijective and detects zero, with its original cocycle evaluation formula. All group, topology and action hypotheses remain explicit.
Named downstream consumer: the original character equivalence constructor and actual continuous characters of the selected character kernel.
-/
import Definitions.Def_MazurTransfer_OriginalTrivialContinuousCohomologyCharacterMapData20261019
noncomputable section
open MazurTransfer ContinuousFirstCohomologyPresentation TrivialContinuousH1Characters
namespace MazurTransfer.TrivialContinuousCohomologyCharactersProofBoundary20261019
end MazurTransfer.TrivialContinuousCohomologyCharactersProofBoundary20261019
/-
Copyright (c) 2026 Vas and contributors. Released under Apache-2.0.
Design boundary: continuous H1 for a GIVEN trivial multiplicative action
identifies with the ACTUAL continuous group homomorphisms. The existing
continuous cocycle quotient and its coefficient group are retained.
Named downstream consumer: arithmetic characters of the subgroup that
trivializes the selected order-13 reflected character.
-/

noncomputable section
namespace MazurTransfer.OriginalTrivialContinuousCohomologyCharactersProof20261019
open MazurTransfer.TrivialContinuousH1Characters
open ContinuousFirstCohomologyPresentation
variable (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M]
  [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M]
variable (htriv : ∀ (g : G) (m : M), g • m = m)
include htriv









theorem toHom_classMap (z : continuousCocycles G M) :
    toHom G M htriv (classMap G M z) = Additive.ofMul (cocycleHom G M htriv z) := rfl

theorem eq_zero_of_toHom_zero (x : H1 G M) (hx : toHom G M htriv x = 0) : x = 0 := by
  revert hx
  refine Quotient.inductionOn x ?_
  intro z hz
  have hz0 : z = 0 := by
    apply Subtype.ext
    apply groupCohomology.cocycles₁_ext
    intro g
    apply Additive.toMul.injective
    exact congrArg (fun h : Additive (G →ₜ* M) => h.toMul g) hz
  change classMap G M z = 0
  rw [hz0, map_zero]

theorem toHom_injective : Function.Injective (toHom G M htriv) := by
  intro x y he
  apply sub_eq_zero.mp
  apply eq_zero_of_toHom_zero G M htriv
  rw [map_sub, he, sub_self]



theorem toHom_surjective : Function.Surjective (toHom G M htriv) := by
  intro f
  exact ⟨classMap G M (homCocycle G M htriv f.toMul), rfl⟩



end MazurTransfer.OriginalTrivialContinuousCohomologyCharactersProof20261019

theorem solution : (∀ (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M] [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (htriv : ∀ (g : G) (m : M), g • m = m) (z : continuousCocycles G M), toHom G M htriv (classMap G M z) = Additive.ofMul (cocycleHom G M htriv z)) ∧ (∀ (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M] [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (htriv : ∀ (g : G) (m : M), g • m = m) (x : H1 G M) (hx : toHom G M htriv x = 0), x = 0) ∧ (∀ (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M] [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (htriv : ∀ (g : G) (m : M), g • m = m), Function.Injective (toHom G M htriv)) ∧ (∀ (G M : Type) [Group G] [CommGroup M] [MulDistribMulAction G M] [TopologicalSpace G] [TopologicalSpace M] [IsTopologicalGroup M] (htriv : ∀ (g : G) (m : M), g • m = m), Function.Surjective (toHom G M htriv)) := by
  exact ⟨MazurTransfer.OriginalTrivialContinuousCohomologyCharactersProof20261019.toHom_classMap, MazurTransfer.OriginalTrivialContinuousCohomologyCharactersProof20261019.eq_zero_of_toHom_zero, MazurTransfer.OriginalTrivialContinuousCohomologyCharactersProof20261019.toHom_injective, MazurTransfer.OriginalTrivialContinuousCohomologyCharactersProof20261019.toHom_surjective⟩
#print axioms solution
