-- Prove2me | solution 1 for GlobalTheory.Survey.UnimodularStandardLattice.trivAt_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:14:07.867648+00:00
-- url     : https://prove2.me/submissions/645324b9-5de5-4720-a28a-6cbb5afd8077

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
theorem _root_.solution (bad : ℕ) : (⟨stdLat E n⟩ : GenLat E n).TrivAt bad :=
  ⟨1, by simp, Submodule.smul_le_right, Submodule.smul_le_right⟩
end GlobalTheory.Survey.UnimodularStandardLattice
