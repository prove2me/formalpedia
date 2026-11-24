-- Prove2me | solution 1 for GlobalTheory.LevelPairing.levRep_mk
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:34.961998+00:00
-- url     : https://prove2.me/submissions/81416c02-1f48-466d-8f4b-1b597dac6d84

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ThShort
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ZeroNotAdmissibleOfRankPos

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
open GlobalTheory GlobalTheory.LevelPairing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
namespace GlobalTheory.LevelPairing
theorem _root_.solution (x : Dw.La) :
    levRep (Submodule.Quotient.mk x : LevQ Dw l) - x ∈ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La) :=
  (Submodule.Quotient.eq _).1 (Classical.choose_spec (Submodule.Quotient.mk_surjective _ (Submodule.Quotient.mk x : LevQ Dw l)))
end GlobalTheory.LevelPairing
