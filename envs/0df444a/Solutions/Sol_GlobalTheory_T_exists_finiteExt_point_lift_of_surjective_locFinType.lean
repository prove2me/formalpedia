-- Prove2me | solution 1 for GlobalTheory.T.exists_finiteExt_point_lift_of_surjective_locFinType
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:18:57.759484+00:00
-- url     : https://prove2.me/submissions/dfdd3a98-2180-4d95-80e4-450100ab0297

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtPointLiftOfSurjectiveLocFinType
import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ThickTransComp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFiniteExtPointLiftOfSurjectiveLocFinTypeStatement
import Theorems.Thm_GlobalTheory_exists_finite_ext_point_lift_of_surjective_lft


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ {X Y : Scheme.{0}} (π : Y ⟶ X), LocallyOfFiniteType π → Function.Surjective π → ∀ (K : Type) [Field K] (x : Sp K ⟶ X), ∃ (K' : Type) (_ : Field K') (σ : K →+* K') (y : Sp K' ⟶ Y), σ.Finite ∧ y ≫ π = spMap σ ≫ x := by
  first | exact @GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft | exact GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft | (intros; apply GlobalTheory.exists_finite_ext_point_lift_of_surjective_lft <;> assumption)
end _root_.GlobalTheory.T
