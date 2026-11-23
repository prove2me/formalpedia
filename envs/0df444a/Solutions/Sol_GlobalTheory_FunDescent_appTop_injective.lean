-- Prove2me | solution 1 for GlobalTheory.FunDescent.appTop_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:00:51.711798+00:00
-- url     : https://prove2.me/submissions/28b64056-3320-4dda-b031-58823f31cac7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Theorems.Thm_GlobalTheory_FunDescent_hom_ext
import Theorems.Thm_GlobalTheory_FunDescent_exists_hom
import Theorems.Thm_GlobalTheory_FunDescent_comp_appTop_apply

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
theorem _root_.solution {X Y : Scheme.{0}} (π : X ⟶ Y) [Epi π] :
    Function.Injective π.appTop.hom := by
  intro a b hab
  obtain ⟨g, rfl⟩ := exists_hom a
  obtain ⟨h, rfl⟩ := exists_hom b
  rw [← comp_appTop_apply, ← comp_appTop_apply] at hab
  rw [(cancel_epi π).1 (hom_ext hab)]
end GlobalTheory.FunDescent
