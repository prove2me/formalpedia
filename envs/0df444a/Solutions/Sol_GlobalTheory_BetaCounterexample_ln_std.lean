-- Prove2me | solution 1 for GlobalTheory.BetaCounterexample.ln_std
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:01:26.459815+00:00
-- url     : https://prove2.me/submissions/7f66722c-24e5-4e7c-86db-259c37038760

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_BetaIsPrincipal

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
open GlobalTheory GlobalTheory.BetaCounterexample
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (c : Coeff l)
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.BetaCounterexample
theorem _root_.solution (n : ℕ) : (⟨stdLat E n⟩ : GenLat E n).Ln = stdLat E n := inf_idem _
end GlobalTheory.BetaCounterexample
