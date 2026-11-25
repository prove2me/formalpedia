-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.IsNormalisation.isIntegralHom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:03:08.479065+00:00
-- url     : https://prove2.me/submissions/dcf8461a-edf4-400b-acbb-4c9d9378d02e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_OpenModelSections
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_LevelActionTransitions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
open AlgebraicGeometry CategoryTheory Limits NumberField MonoidalCategory CartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.IndefiniteRowSideFullHecke.CoefficientFieldBaseChange GlobalTheory.IndefiniteRowSideFullHecke.OpenModelSections
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
namespace IsNormalisation
theorem _root_.solution {U Z Y : Scheme.{0}} {i : U ⟶ Z} {p : Z ⟶ Y} (h : IsNormalisation i p) :
    IsIntegralHom p := by
  obtain ⟨_, _, e, -, he⟩ := h
  rw [← he]; infer_instance
end IsNormalisation
end GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
