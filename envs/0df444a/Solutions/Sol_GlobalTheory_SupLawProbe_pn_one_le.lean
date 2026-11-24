-- Prove2me | solution 1 for GlobalTheory.SupLawProbe.pn_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:43:05.685937+00:00
-- url     : https://prove2.me/submissions/d04ac53f-e4d4-42ef-880f-86e84013c7c8

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
import Theorems.Thm_GlobalTheory_SupLawProbe_evR_of_not_ft
import Theorems.Thm_GlobalTheory_SupLawProbe_evR_one
import Theorems.Thm_GlobalTheory_SupLawProbe_ex_zero
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
theorem _root_.solution (σ : c.F →+* ℂ) (y : FrPt Xo c (CAt σ)) : pn σ (fn σ) (ex Dw 0 0) 1 y ≤ 1 := by
  show cabs (evR Xo c 1 y) * ∏ i, |fn σ y i|⁻¹ ^ ex Dw 0 0 i ≤ 1
  simp only [ex_zero, pow_zero, Finset.prod_const_one, mul_one]
  by_cases hy : FT y
  · rw [evR_one _ hy, cabs_one]
  · rw [evR_of_not_ft _ _ hy, cabs_zero]; exact zero_le_one
end GlobalTheory.SupLawProbe
