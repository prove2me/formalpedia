-- Prove2me | solution 1 for GlobalTheory.HeightEnds.gramDet_square
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:47.042978+00:00
-- url     : https://prove2.me/submissions/7ca543cc-e898-485e-a804-de5ab6274c02

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsBasisMem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_RelIndexSpanNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_ExistsPosLeLatticeHeightBotTop

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up MeasureTheory Topology
open scoped ComplexOrder ENNReal Matrix
open GlobalTheory GlobalTheory.HeightEnds
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace GlobalTheory.HeightEnds
theorem _root_.solution {r : ℕ} (N : Matrix (Fin r) (Fin r) ℂ) :
    (Nᴴ * N).det.re = ‖N.det‖ ^ 2 := by
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def, Complex.conj_mul']
  norm_cast
end GlobalTheory.HeightEnds
