-- Prove2me | solution 1 for GlobalTheory.TorusNil.exists_retraction
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T12:14:34.054699+00:00
-- url     : https://prove2.me/submissions/611a8e63-b941-4a6f-910c-a61ff2cda98d

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
theorem _root_.solution : ∃ r : AddMonoidAlgebra A (X × X) →ₗ[A] AddMonoidAlgebra A X,
    ∀ d, r (dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X)) d -
      (dm A X (AddMonoidHom.inl X X) d + dm A X (AddMonoidHom.inr X X) d)) = d := by
  classical
  let r : AddMonoidAlgebra A (X × X) →ₗ[A] AddMonoidAlgebra A X :=
    (AddMonoidAlgebra.basis (X × X) A).constr A (fun p =>
      if p.1 = p.2 then (if p.1 = 0 then -AddMonoidAlgebra.single 0 1 else
        AddMonoidAlgebra.single p.1 1) else 0)
  have hr : ∀ p : X × X, r (AddMonoidAlgebra.single p 1) =
      if p.1 = p.2 then (if p.1 = 0 then -AddMonoidAlgebra.single 0 1 else
        AddMonoidAlgebra.single p.1 1) else 0 := fun p =>
    (AddMonoidAlgebra.basis (X × X) A).constr_basis A _ p
  refine ⟨r, fun d => ?_⟩
  have : r ∘ₗ ((dm A X ((AddMonoidHom.id X).prod (AddMonoidHom.id X))).toLinearMap -
      ((dm A X (AddMonoidHom.inl X X)).toLinearMap +
        (dm A X (AddMonoidHom.inr X X)).toLinearMap)) = LinearMap.id := by
    apply (AddMonoidAlgebra.basis X A).ext
    intro x
    by_cases hx : x = 0
    · simp [hr, hx]
    · simp [hr, hx, Ne.symm hx]
  exact LinearMap.congr_fun this d
end GlobalTheory.TorusNil
