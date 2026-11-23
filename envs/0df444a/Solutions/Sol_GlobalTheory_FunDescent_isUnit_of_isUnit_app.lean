-- Prove2me | solution 1 for GlobalTheory.FunDescent.isUnit_of_isUnit_app
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:40:32.95881+00:00
-- url     : https://prove2.me/submissions/62d75b7f-d8d9-4616-a363-dada0565fe4b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend

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
open GlobalTheory GlobalTheory.FunDescent
namespace GlobalTheory.FunDescent
theorem _root_.solution {X Y : Scheme.{0}} (π : X ⟶ Y) [Surjective π] (U : Y.Opens)
    (a : Γ(Y, U)) (ha : IsUnit ((π.app U).hom a)) : IsUnit a := by
  refine Y.toRingedSpace.isUnit_of_isUnit_germ U a fun y hy => ?_
  obtain ⟨x, rfl⟩ := π.surjective y
  have h1 : X.basicOpen ((π.app U).hom a) = π ⁻¹ᵁ U := X.basicOpen_of_isUnit ha
  have h2 : x ∈ π ⁻¹ᵁ (Y.basicOpen a) := by
    rw [Scheme.preimage_basicOpen]
    exact h1.ge hy
  exact (Y.mem_basicOpen a (π x) hy).1 h2
end GlobalTheory.FunDescent
