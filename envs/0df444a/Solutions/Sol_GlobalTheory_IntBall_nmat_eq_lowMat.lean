-- Prove2me | solution 1 for GlobalTheory.IntBall.nmat_eq_lowMat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:40:33.773834+00:00
-- url     : https://prove2.me/submissions/3b769b1f-1e5b-4a69-bf20-40ff2e20a45c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_ArakelovInstances_IsStrictDom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NmatEqLowMat

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.IntBall
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal Matrix
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
namespace GlobalTheory.IntBall
theorem _root_.solution (X : Data E r) (z : V (nd X)) (τ : X.Ψ) :
    (Matrix.of (nmat X z τ) : Matrix (Fin r) (Fin r) ℂ) = lowMat (zOf X z τ) := by
  ext a b
  simp only [Matrix.of_apply, nmat, lowMat, zOf]
end GlobalTheory.IntBall
