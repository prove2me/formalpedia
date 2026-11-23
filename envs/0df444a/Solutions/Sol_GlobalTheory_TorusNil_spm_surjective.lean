-- Prove2me | solution 1 for GlobalTheory.TorusNil.spm_surjective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:08:47.284883+00:00
-- url     : https://prove2.me/submissions/7751207c-48cd-46f5-bc12-49976d26bfd1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory
open GlobalTheory.TorusNil
variable {A : Type} [CommRing A]
variable {C D E : Type} [CommRing C] [Algebra A C] [CommRing D] [Algebra A D]
  [CommRing E] [Algebra A E]
namespace GlobalTheory.TorusNil
theorem _root_.solution (g : sp A D ⟶ sp A C) : ∃ φ : C →ₐ[A] D, spm φ = g := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (R := CommRingCat.of C) (S := CommRingCat.of D) g.left
  have hw : CommRingCat.ofHom (algebraMap A C) ≫ φ = CommRingCat.ofHom (algebraMap A D) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ]
    exact Over.w g
  refine ⟨⟨φ.hom, fun a => congrArg
    (fun g : CommRingCat.of A ⟶ CommRingCat.of D => g.hom a) hw⟩, ?_⟩
  apply Over.OverMorphism.ext
  exact hφ
end GlobalTheory.TorusNil
