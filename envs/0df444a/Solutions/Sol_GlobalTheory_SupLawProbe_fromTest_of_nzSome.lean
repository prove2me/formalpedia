-- Prove2me | solution 1 for GlobalTheory.SupLawProbe.fromTest_of_nzSome
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:59:57.904801+00:00
-- url     : https://prove2.me/submissions/882124e8-a295-4475-acc2-8052f72d143a

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
import Theorems.Thm_GlobalTheory_SupLawProbe_evR_of_not_ft

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
theorem _root_.solution {f : Rul Xo c} (hN : NZSome h f) : ∃ Z, evC h Z f ≠ 0 ∧ FT (genFr h Z) := by
  obtain ⟨Z, hZ⟩ := hN
  refine ⟨Z, hZ, ?_⟩
  by_contra hg
  exact hZ (evR_of_not_ft _ _ hg)
end GlobalTheory.SupLawProbe
