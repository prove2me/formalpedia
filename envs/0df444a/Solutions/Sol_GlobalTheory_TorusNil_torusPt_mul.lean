-- Prove2me | solution 1 for GlobalTheory.TorusNil.torusPt_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:36:08.689737+00:00
-- url     : https://prove2.me/submissions/6fb47142-a2f8-43ca-acb2-847b1cfb0224

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
variable (A) (X : Type) [AddCommGroup X]
namespace GlobalTheory.TorusNil
theorem _root_.solution {C : Type} [CommRing C] [Algebra A C] (χ χ' : Multiplicative X →* C) :
    torusPt A X (χ * χ') = torusPt A X χ * torusPt A X χ' := by
  letI : Algebra (ULift.{0} ℤ) C := ULift.algebra' ℤ C
  have h : WithConv.toConv (AddMonoidAlgebra.lift (ULift.{0} ℤ) C X (χ * χ')) =
      WithConv.toConv (AddMonoidAlgebra.lift (ULift.{0} ℤ) C X χ) *
        WithConv.toConv (AddMonoidAlgebra.lift (ULift.{0} ℤ) C X χ') := by
    apply WithConv.ofConv_injective
    ext x
    simp
  unfold torusPt
  rw [h, map_mul, Functor.map_mul]
  exact MonObj.comp_mul _ _ _
end GlobalTheory.TorusNil
