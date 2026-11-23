-- Prove2me | solution 1 for GlobalTheory.TorusNil.torusPt_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:16:15.928489+00:00
-- url     : https://prove2.me/submissions/3987a885-b0e1-42b1-93dd-75791ac2025a

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Theorems.Thm_GlobalTheory_TorusNil_pullback_map_fst

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
variable (A) (X : Type) [AddCommGroup X]
namespace GlobalTheory.TorusNil
theorem _root_.solution {C : Type} [CommRing C] [Algebra A C] (χ : Multiplicative X →* C) :
    ∃ φ : AddMonoidAlgebra (ULift.{0} ℤ) X →+* C,
      (∀ x, φ (AddMonoidAlgebra.single x 1) = χ (Multiplicative.ofAdd x)) ∧
      (torusPt A X χ).left ≫ pullback.fst (splitTorusAff ZU X).hom (toZ _) =
        Spec.map (CommRingCat.ofHom φ) := by
  letI : Algebra (ULift.{0} ℤ) C := ULift.algebra' ℤ C
  refine ⟨(AddMonoidAlgebra.lift (ULift.{0} ℤ) C X χ).toRingHom, fun x => by simp, ?_⟩
  refine (pullback_map_fst _ _).trans ?_
  erw [pullback.lift_fst_assoc]
  exact Category.id_comp _
end GlobalTheory.TorusNil
