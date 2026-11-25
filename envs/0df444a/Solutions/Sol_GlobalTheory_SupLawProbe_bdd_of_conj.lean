-- Prove2me | solution 1 for GlobalTheory.SupLawProbe.bdd_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T18:13:44.389183+00:00
-- url     : https://prove2.me/submissions/a348ae34-77b7-4e0e-898f-2b9ef99608a0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AxHSup
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_FrameCharts
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_LevelGroupExamples_ChosenEqOfAllRules
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_HeightSurvey_FromTestIffOfValAtCx
import Theorems.Thm_GlobalTheory_SupLawProbe_pn_le_conj

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
theorem _root_.solution
    (hB : BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((starRingEnd ℂ).comp σ) (fn _)
      (ex Dw a n) f) :
    BddAt (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) f := by
  obtain ⟨b, hb⟩ := hB
  exact ⟨b, Set.forall_mem_range.2 fun y => (pn_le_conj hWD σ cj hcj htr hS y).trans (hb ⟨cj y, rfl⟩)⟩
end GlobalTheory.SupLawProbe
