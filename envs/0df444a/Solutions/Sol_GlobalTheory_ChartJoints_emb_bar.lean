-- Prove2me | solution 1 for GlobalTheory.ChartJoints.emb_bar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:20.1388+00:00
-- url     : https://prove2.me/submissions/1c3129bc-8f65-4115-9782-c00dd7b7cc2b

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_ThExprUniqOfChartIndep2
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_JetSurvey_BalancedPairs

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.ChartJoints
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.ChartJoints
theorem _root_.solution (H : Host E) (τ : E →+* ℂ) (a : 𝓞 E) :
    τ ((H.bar a : 𝓞 E) : E) = ComplexEmbedding.conjugate τ (a : E) := by
  rw [H.bar_eq, IsCMField.complexEmbedding_complexConj]
  rfl
end GlobalTheory.ChartJoints
