-- Prove2me | solution 1 for GlobalTheory.GrpSep.rmul_oneF
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:53:11.336636+00:00
-- url     : https://prove2.me/submissions/00ebd858-c3ca-4cc3-8200-c403e660b042

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_InterpStatementPfH
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsLeNormDev

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
open GlobalTheory GlobalTheory.GrpSep
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.GrpSep
theorem _root_.solution {Ψ : Finset (E →+* ℂ)} {r : ℕ} (x : Frame Ψ r) : rmul x (oneF Ψ r) = x := by
  funext τ
  change mat x τ * (1 : Matrix (Fin r) (Fin r) ℂ) = mat x τ
  exact Matrix.mul_one _
end GlobalTheory.GrpSep
