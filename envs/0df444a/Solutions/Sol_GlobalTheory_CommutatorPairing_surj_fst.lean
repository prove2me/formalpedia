-- Prove2me | solution 1 for GlobalTheory.CommutatorPairing.surj_fst
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:02:36.197604+00:00
-- url     : https://prove2.me/submissions/150ff1a8-fa08-49ec-ad06-c9d74e7534ff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueWeilIs
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_surj_snd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.CommutatorPairing
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]
namespace GlobalTheory.CommutatorPairing
theorem _root_.solution (hG : GlobalFnsSt) (hA : IsAbelianScheme A) (T : Over S) :
    Function.Surjective (fst T A).left.appTop.hom := by
  have e : (fst T A).left = (β_ T A).hom.left ≫ (snd A T).left := by
    rw [← Over.comp_left, braiding_hom_snd]
  rw [e]
  refine surj_comp ?_ (surj_snd hG hA T)
  have : IsIso (β_ T A).hom.left := inferInstanceAs (IsIso ((Over.forget S).map (β_ T A).hom))
  have : IsIso (β_ T A).hom.left.appTop := inferInstanceAs (IsIso ((β_ T A).hom.left.app ⊤))
  exact (ConcreteCategory.bijective_of_isIso (β_ T A).hom.left.appTop).2
end GlobalTheory.CommutatorPairing
