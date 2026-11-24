-- Prove2me | solution 1 for GlobalTheory.Survey.StandardLatticeGoodPlace.mem_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T20:59:53.862576+00:00
-- url     : https://prove2.me/submissions/0992aa98-c8f9-48eb-b096-4fe9e842fc03

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
theorem _root_.solution {n : ℕ} (v : Fin n → E) :
    v ∈ stdLat E n ↔ ∀ j, v j ∈ (algebraMap (𝓞 E) E).range := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one, RingHom.mem_range]
end GlobalTheory.Survey.StandardLatticeGoodPlace
