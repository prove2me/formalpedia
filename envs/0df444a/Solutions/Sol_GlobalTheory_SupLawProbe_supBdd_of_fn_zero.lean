-- Prove2me | solution 1 for GlobalTheory.SupLawProbe.supBdd_of_fn_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:13:00.201084+00:00
-- url     : https://prove2.me/submissions/05ab81cd-b4cd-4d13-956e-cf4fa0a4eb18

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
import Theorems.Thm_GlobalTheory_SupNormExample_bddAt_of_fnorm_zero


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
theorem _root_.solution (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : n ≠ 0) (f : Rul Xo c) :
    SupBdd Xo c (fun _ _ _ => 0) a n f ∧ ∀ σ, supR Xo c (fun _ _ _ => 0) σ a n f = 0 :=
  ⟨fun σ => (SupNormExample.bddAt_of_fnorm_zero _ _ σ (ex Dw a n) none hn f).1,
   fun σ => (SupNormExample.bddAt_of_fnorm_zero _ _ σ (ex Dw a n) none hn f).2⟩
end GlobalTheory.SupLawProbe
