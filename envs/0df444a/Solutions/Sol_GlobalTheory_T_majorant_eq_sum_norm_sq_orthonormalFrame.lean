-- Prove2me | solution 1 for GlobalTheory.T.majorant_eq_sum_norm_sq_orthonormalFrame
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:13:32.452217+00:00
-- url     : https://prove2.me/submissions/db30460d-2b4a-4c49-a297-cde8d21a02f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrame
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_WeightFunctionOnFrames
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_MajorantEqSumNormSqOrthonormalFrameStatement
import Theorems.Thm_GlobalTheory_MajorantOrthFrame_maj_eq_sum_norm_sq_of_isOrth


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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
namespace _root_.GlobalTheory.T
theorem _root_.solution : (∀ (r : ℕ) (X : Data E r) (x : Frame X.Ψ r), IsOrth X x → (∀ τ : X.Ψ, (mat x τ).det ≠ 0) ∧ ∀ (τ : X.Ψ) (v : Fin r → ℂ), X.maj x τ v = ∑ a, ‖((mat x τ)⁻¹.mulVec v) a‖ ^ 2) := by
  first | exact @GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth | exact GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth | (intros; apply GlobalTheory.MajorantOrthFrame.maj_eq_sum_norm_sq_of_isOrth <;> assumption)
end _root_.GlobalTheory.T
