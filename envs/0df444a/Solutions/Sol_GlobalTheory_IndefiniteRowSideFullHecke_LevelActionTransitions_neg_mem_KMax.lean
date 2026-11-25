-- Prove2me | solution 1 for GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions.neg_mem_KMax
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:00:14.818974+00:00
-- url     : https://prove2.me/submissions/86763dc0-773b-47ff-b369-887700357fb0

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
variable (D : Datum H)
namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
theorem _root_.solution : (fun n => LinearEquiv.neg (𝓞 E)) ∈ KMax D := by
  have h1 := (KMax D).one_mem
  refine ⟨fun n m a b h => h1.1 n m (-a) b h, fun n a b a' b' ha hb => ?_⟩
  simpa using h1.2 n (-a) (-b) a' b' ha hb
end GlobalTheory.IndefiniteRowSideFullHecke.LevelActionTransitions
