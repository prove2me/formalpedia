-- Prove2me | solution 1 for GlobalTheory.IsogenySum.continuous_thetaSectionPointwiseNormSq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:13:29.774526+00:00
-- url     : https://prove2.me/submissions/2398473d-f2a0-4e19-bf91-76cf213dafb7

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_FockTranslationLaws
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_IntegrableOnFundamentalDomainOfContinuous
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ContinuousThetaSectionPointwiseNormSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Complex ReciprocityTheory.ChartRestriction.G.I2 MeasureTheory
open GlobalTheory.IsogenySum
open FockTranslation
variable {ι : Type} [Fintype ι]
namespace GlobalTheory.IsogenySum
theorem _root_.solution (Y : GT ι) {F : EuclideanSpace ℂ ι → ℂ} (hF : Continuous F) :
    Continuous (Y.ptN2 1 F) := by
  unfold GT.ptN2
  fun_prop
end GlobalTheory.IsogenySum
