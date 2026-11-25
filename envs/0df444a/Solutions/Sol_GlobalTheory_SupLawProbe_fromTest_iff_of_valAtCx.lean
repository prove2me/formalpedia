-- Prove2me | solution 1 for GlobalTheory.SupLawProbe.fromTest_iff_of_valAtCx
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T18:11:17.03512+00:00
-- url     : https://prove2.me/submissions/639447e7-738a-4a86-ad19-d74dcb08205b

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
import Theorems.Thm_GlobalTheory_SupLawProbe_evR_of_not_ft
import Theorems.Thm_GlobalTheory_SupLawProbe_evR_one
import Theorems.Thm_GlobalTheory_SupLawProbe_one_mem_sec
import Theorems.Thm_GlobalTheory_SupLawProbe_cabs_one
import Theorems.Thm_GlobalTheory_SupLawProbe_cabs_zero

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
theorem _root_.solution (hcx : ValAtCx h yP) (Z : Comp Xo c) (P : Om Z →+* ℂ) :
    FT (genFr h Z) ↔ FT (yP Z P) := by
  have h1 := hcx Z P 0 0 1 one_mem_sec
  unfold evC at h1
  constructor
  · intro hg
    by_contra hy
    rw [evR_one _ hg, evR_of_not_ft _ _ hy, map_one, norm_one, cabs_zero] at h1
    exact one_ne_zero h1
  · intro hy
    by_contra hg
    rw [evR_one _ hy, evR_of_not_ft _ _ hg, map_zero, norm_zero, cabs_one] at h1
    exact zero_ne_one h1
end GlobalTheory.SupLawProbe
