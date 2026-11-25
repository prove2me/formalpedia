-- Prove2me | solution 1 for GlobalTheory.SW.FourierJ.Row.qv_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:06:22.415716+00:00
-- url     : https://prove2.me/submissions/b29a6650-143c-4b0f-a417-9474961f0887

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EchEqOneIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsEqTransposeMulDiagonalMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_PoissonSummationThetaSeriesRowTermCoset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.SW.FourierJ
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.FourierJ GlobalTheory.SW.FourierJ.Row
variable {ι : Type} [Fintype ι]
omit [Fintype ι]
namespace GlobalTheory.SW.FourierJ.Row
theorem _root_.solution (v : ι → ℚ) (r : ℚ) : qv (r • v) = (r : ℂ) • qv v := by
  ext i; simp [qv]
end GlobalTheory.SW.FourierJ.Row
