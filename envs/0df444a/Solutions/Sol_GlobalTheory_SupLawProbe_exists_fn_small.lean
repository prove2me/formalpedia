-- Prove2me | solution 1 for GlobalTheory.SupLawProbe.exists_fn_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:48.102824+00:00
-- url     : https://prove2.me/submissions/9e69095e-8994-4881-abb8-200c5d667c74

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
import Theorems.Thm_GlobalTheory_SupNormExample_exists_fnorm_small


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
    ∃ fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ,
      FnNe Xo c fn ∧ SupBdd Xo c fn a n f ∧ ∀ σ, supR Xo c fn σ a n f ≤ 1 := by
  choose g hg using fun σ : c.F →+* ℂ =>
    SupNormExample.exists_fnorm_small (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ
      (ex Dw a n) none hn f
  exact ⟨g, fun σ y i => ((hg σ).1 y i).ne', fun σ => (hg σ).2.1, fun σ => (hg σ).2.2⟩
end GlobalTheory.SupLawProbe
