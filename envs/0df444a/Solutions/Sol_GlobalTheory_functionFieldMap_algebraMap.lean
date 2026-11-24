-- Prove2me | solution 1 for GlobalTheory.functionFieldMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:41:16.419256+00:00
-- url     : https://prove2.me/submissions/28ab1d56-7016-417a-9f06-1ce404cd0941

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring
import Theorems.Thm_GlobalTheory_specMap_functionFieldMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
noncomputable section
open GlobalTheory
variable {X X' S : Scheme.{u}} [IsIntegral X] [IsIntegral X']
variable {W : ValuationSubring X.functionField} {x : X}
namespace GlobalTheory
theorem _root_.solution (f : X ⟶ X') [IsDominant f] (x : X)
    (a : X'.presheaf.stalk (f x)) :
    functionFieldMap f (algebraMap _ X'.functionField a) =
      algebraMap _ X.functionField (f.stalkMap x a) := by
  have e : Spec.map (CommRingCat.ofHom (algebraMap (X'.presheaf.stalk (f x)) X'.functionField) ≫
        CommRingCat.ofHom (functionFieldMap f)) ≫ X'.fromSpecStalk _ =
      Spec.map (f.stalkMap x ≫ CommRingCat.ofHom
        (algebraMap (X.presheaf.stalk x) X.functionField)) ≫ X'.fromSpecStalk _ := by
    refine Eq.trans ?_ (congrArg (· ≫ X'.fromSpecStalk (f x)) (Spec.map_comp _ _)).symm
    rw [Spec.map_comp, Category.assoc, Category.assoc,
      specAlgebraMap_fromSpecStalk, specMap_functionFieldMap,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← specAlgebraMap_fromSpecStalk x]
    exact Category.assoc _ _ _
  exact congr($(Spec.map_injective ((cancel_mono _).mp e)) a)
end GlobalTheory
