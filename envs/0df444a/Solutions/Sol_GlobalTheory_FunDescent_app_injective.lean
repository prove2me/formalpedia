-- Prove2me | solution 1 for GlobalTheory.FunDescent.app_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T16:44:58.392798+00:00
-- url     : https://prove2.me/submissions/db311f12-8212-4191-8669-d32af971eda4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Theorems.Thm_GlobalTheory_FunDescent_appTop_injective
import Theorems.Thm_GlobalTheory_FunDescent_res_bijective
import Theorems.Thm_GlobalTheory_FunDescent_res_square_apply

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
theorem _root_.solution {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π] (U : Y.Opens) :
    Function.Injective (π.app U).hom := by
  have : Surjective (π ∣_ U) := IsZariskiLocalAtTarget.restrict (P := @Surjective) ‹_› U
  have : Epi (π ∣_ U) := Flat.epi_of_flat_of_surjective _
  intro a b hab
  apply (res_bijective U).1
  apply appTop_injective (π ∣_ U)
  rw [res_square_apply, res_square_apply, hab]
end GlobalTheory.FunDescent
