-- Prove2me | solution 1 for GlobalTheory.FunDescent.res_square
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:47:08.42988+00:00
-- url     : https://prove2.me/submissions/2912305b-aec9-4809-a5bf-10f2a5716615

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Theorems.Thm_GlobalTheory_FunDescent_res_comp_appTop

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
theorem _root_.solution {X Y : Scheme.{0}} (π : X ⟶ Y) (U : Y.Opens) :
    res U ≫ (π ∣_ U).appTop = π.app U ≫ res (π ⁻¹ᵁ U) := by
  rw [res_comp_appTop U (π ∣_ U) ((π ⁻¹ᵁ U).ι ≫ π) (morphismRestrict_ι π U).symm (by simp),
    res, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
end GlobalTheory.FunDescent
