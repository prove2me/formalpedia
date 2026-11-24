-- Prove2me | solution 1 for GlobalTheory.SupLawProbe.pn_le_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:14:53.664325+00:00
-- url     : https://prove2.me/submissions/9b3b65df-40e4-4151-99d4-510d0985b4c3

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
import Theorems.Thm_GlobalTheory_SupLawProbe_evR_of_not_ft
import Theorems.Thm_GlobalTheory_SupLawProbe_evR_map
import Theorems.Thm_GlobalTheory_SupLawProbe_cabs_zero
import Theorems.Thm_Formalism_L2_Pj_ptNorm_nonneg
import Theorems.Thm_GlobalTheory_SupNormExample_ptNorm_conj


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
variable (hWD : EvalWD (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z))
  (σ : c.F →+* ℂ) (cj : FrPt Xo c (CAt σ) → FrPt Xo c (CAt ((starRingEnd ℂ).comp σ)))
  (hcj : ∀ y, FrMap (SupNormExample.conjAt σ) y (cj y))
  (htr : ∀ y i, |fn _ (cj y) i| = |fn σ y i|) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {f : Rul Xo c}
  (hS : f ∈ sec Xo c a n)
include hWD hcj htr hS
namespace GlobalTheory.SupLawProbe
theorem _root_.solution (y : FrPt Xo c (CAt σ)) :
    pn σ (fn σ) (ex Dw a n) f y ≤ pn _ (fn _) (ex Dw a n) f (cj y) := by
  by_cases hy : FT y
  · exact (SupNormExample.ptNorm_conj _ _ σ (fn σ) (fn _) (ex Dw a n) f y (cj y)
      (evR_map hWD f hS.1 (SupNormExample.conjAt σ) y hy (cj y) (hcj y)) (htr y)).ge
  · refine le_trans (le_of_eq ?_) (ptNorm_nonneg _ _ _ _ _ _ _)
    show cabs (evR Xo c f y) * _ = 0
    rw [evR_of_not_ft _ _ hy, cabs_zero, zero_mul]
end GlobalTheory.SupLawProbe
