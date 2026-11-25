-- Prove2me | solution 1 for GlobalTheory.Survey.UnimodularStandardLattice.mem_stdLat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:14:03.189906+00:00
-- url     : https://prove2.me/submissions/f9f718b9-d10c-4306-98ee-0f7c64be3473

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_ThetaSpanAdjoint
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_UnimodularStandardLattice

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
open GlobalTheory GlobalTheory.Survey GlobalTheory.Survey.UnimodularStandardLattice
open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}
omit [IsCMField E]
namespace GlobalTheory.Survey.UnimodularStandardLattice
theorem _root_.solution (v : Fin n → E) : v ∈ stdLat E n ↔ ∀ j, ∃ b : 𝓞 E, (b : E) = v j := by
  simp [stdLat, Submodule.mem_pi, Submodule.mem_one]
end GlobalTheory.Survey.UnimodularStandardLattice
