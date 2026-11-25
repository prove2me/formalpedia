-- Prove2me | solution 1 for GlobalTheory.SupLawProbe.laws_of_no_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:11:19.882216+00:00
-- url     : https://prove2.me/submissions/af921078-7d97-4abb-966f-03441b0e109b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.SupLawProbe
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.T0 Formalism.L2.Pj
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
variable {h : GenFrEx Xo c} {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ}
  {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))}
namespace GlobalTheory.SupLawProbe
theorem _root_.solution (hne : IsEmpty (Comp Xo c)) (f : Rul Xo c) :
    PTNe Xo c ∧ ValAtCx h yP ∧ ¬ NZSome h f :=
  ⟨fun Z => hne.elim Z, fun Z => hne.elim Z, fun ⟨Z, _⟩ => hne.elim Z⟩
end GlobalTheory.SupLawProbe
