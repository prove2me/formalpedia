-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes.isAbelianScheme_unit
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:40:21.253867+00:00
-- url     : https://prove2.me/submissions/588d3beb-ea8a-409f-8331-8fca408e617e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_SplitTori_SplitTorusAff
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_AbelianSchemeLaw_SemiAbelianSchemes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
open ReciprocityTheory.ChartRestriction.G.Semi
namespace GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
theorem _root_.solution (S : Scheme.{u}) : IsAbelianScheme (𝟙_ (Over S)) where
  smooth := inferInstanceAs (Smooth (𝟙 S))
  proper := inferInstanceAs (IsProper (𝟙 S))
  geometricallyConnected := by
    change GeometricallyConnected (𝟙 S)
    refine ⟨fun K _ y Z fst snd h => ?_⟩
    have : IsIso snd := h.isIso_snd_of_isIso
    exact (Scheme.homeoOfIso (asIso snd)).symm.surjective.connectedSpace
      (Scheme.homeoOfIso (asIso snd)).symm.continuous
  comm := inferInstance
end GlobalTheory.IndefiniteRowSideFullHecke.SemiAbelianSchemes
