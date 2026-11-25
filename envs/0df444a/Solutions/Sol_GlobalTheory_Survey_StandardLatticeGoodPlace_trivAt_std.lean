-- Prove2me | solution 1 for GlobalTheory.Survey.StandardLatticeGoodPlace.trivAt_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:16:29.826182+00:00
-- url     : https://prove2.me/submissions/53693cd6-d7bb-42aa-af90-fbed45b61d42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_ExistenceTori_ThetaIntegralityAtPlaces
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_StandardLatticeGoodPlace

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.StandardLatticeGoodPlace
open NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.ThetaIntegralityAtPlaces
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.Survey.StandardLatticeGoodPlace
theorem _root_.solution (n k : ℕ) : GenLat.TrivAt (⟨stdLat E n⟩ : GenLat E n) k := by
  exact ⟨1, Nat.coprime_one_left _, Submodule.smul_le_right, Submodule.smul_le_right⟩
end GlobalTheory.Survey.StandardLatticeGoodPlace
