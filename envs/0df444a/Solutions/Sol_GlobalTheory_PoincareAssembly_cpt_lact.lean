-- Prove2me | solution 1 for GlobalTheory.PoincareAssembly.cpt_lact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:59:31.636587+00:00
-- url     : https://prove2.me/submissions/43c35bb5-ce38-4b85-8d1a-b632448d9e6c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_OntoStatementPfS
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_PoinStatementOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix
open GlobalTheory GlobalTheory.PoincareAssembly
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.PoincareAssembly
theorem _root_.solution {r : ℕ} (X : Data E r) (γ : GL (Fin r) E) (x : Frame X.Ψ r) (z : V (nd X)) :
    cpt X (lact γ x) z = lact γ (cpt X x z) := by
  funext τ
  show (mat (lact γ x) τ * mat (nmat X z) τ : Matrix (Fin r) (Fin r) ℂ) =
    ((γ : Matrix (Fin r) (Fin r) E).map τ.1 * mat (cpt X x z) τ : Matrix (Fin r) (Fin r) ℂ)
  simp only [mat, lact, cpt, rmul]
  exact Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (Matrix.of (x τ))
    (Matrix.of (nmat X z τ))
end GlobalTheory.PoincareAssembly
