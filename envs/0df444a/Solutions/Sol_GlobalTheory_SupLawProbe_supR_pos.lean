-- Prove2me | solution 1 for GlobalTheory.SupLawProbe.supR_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:34:03.703937+00:00
-- url     : https://prove2.me/submissions/ed3db54a-dd77-4a3a-a7c8-74fd2b5811d0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
import Theorems.Thm_Formalism_L2_Pj_nrmC_pos
import Theorems.Thm_Formalism_L2_Pj_nrmC_valC_le
import Theorems.Thm_Formalism_L2_Pj_valC_mem


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
theorem _root_.solution [Fintype (Comp Xo c)] (hfn : FnNe Xo c fn) (hPT : PTNe Xo c) (hcx : ValAtCx h yP)
    {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c} (hS : f ∈ sec Xo c a n) (hB : SupBdd Xo c fn a n f)
    (hN : NZSome h f) (σ : c.F →+* ℂ) : 0 < supR Xo c fn σ a n f := by
  obtain ⟨Z, hZ⟩ := hN
  obtain ⟨P, hP⟩ := hPT Z σ
  have h1 := nrmC_valC_le hcx hS hB Z P
  have hP' : sgOf P = σ := hP
  rw [hP'] at h1
  exact lt_of_lt_of_le (nrmC_pos fn (yP Z) hfn P (valC_mem h a n f Z) (valC_ne_zero hZ)) h1
end GlobalTheory.SupLawProbe
