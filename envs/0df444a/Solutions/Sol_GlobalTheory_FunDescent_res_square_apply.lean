-- Prove2me | solution 1 for GlobalTheory.FunDescent.res_square_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:06:03.928078+00:00
-- url     : https://prove2.me/submissions/52b02259-a213-4289-80fd-fd26a4e5f55d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Theorems.Thm_GlobalTheory_FunDescent_res_square

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
theorem _root_.solution {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) (a : Γ(Y, U)) :
    (π ∣_ U).appTop.hom ((res U).hom a) = (res (π ⁻¹ᵁ U)).hom ((π.app U).hom a) :=
  congrArg (fun ψ => ψ.hom a) (res_square π U)
end GlobalTheory.FunDescent
