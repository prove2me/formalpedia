-- Prove2me | solution 1 for GlobalTheory.specMap_functionFieldMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:33:49.410833+00:00
-- url     : https://prove2.me/submissions/688756d2-5130-424f-83d3-de1852b555a3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsValuationSubringDominatingSubring

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
theorem _root_.solution (f : X ⟶ X') [IsDominant f] :
    Spec.map (CommRingCat.ofHom (functionFieldMap f)) ≫ genericFieldPoint X' =
      genericFieldPoint X ≫ f := by
  refine (congrArg (· ≫ X'.fromSpecStalk (genericPoint X')) (Spec.map_comp _ _)).trans ?_
  rw [Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  rfl
end GlobalTheory
