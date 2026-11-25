-- Prove2me | solution 1 for GlobalTheory.ThetaSumBound.prod_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:21:12.117825+00:00
-- url     : https://prove2.me/submissions/7fdc333b-70ab-4a61-8783-9d8d8d8526e3

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtData
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ModerateCoefficientPositivity
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TorusAtDataPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsThetaRunParametersUniformTorusStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FirstMinimumSqMulIInfHeightLeCard

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory GlobalTheory.ThetaSumBound
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [IsCMField E]
namespace GlobalTheory.ThetaSumBound
theorem _root_.solution (T : PT E) (s : (Fin 1 → Vsp T.dim) → ℂ) (a : Fin T.r → Vsp T.dim) :
    ∏ b, T.ptN2 1 s (fun _ => a b) / T.l2 1 s =
      (∏ j, Real.sqrt (T.ptN2 1 s fun _ => a j) / Real.sqrt (T.l2 1 s)) ^ 2 := by
  have hp : ∀ v, 0 ≤ T.ptN2 1 s v := fun v => by unfold PT.ptN2; positivity
  have hl : 0 ≤ T.l2 1 s := MeasureTheory.integral_nonneg hp
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [div_pow, Real.sq_sqrt (hp _), Real.sq_sqrt hl]
end GlobalTheory.ThetaSumBound
