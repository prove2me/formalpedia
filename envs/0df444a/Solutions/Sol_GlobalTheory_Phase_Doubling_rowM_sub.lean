-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.rowM_sub
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:25:57.327304+00:00
-- url     : https://prove2.me/submissions/9a3e610c-e925-4afd-ac23-4f97ff7d14ff

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real Kronecker
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.Doubling
noncomputable section
variable {n g : ℕ}
namespace GlobalTheory.Phase.Doubling
theorem _root_.solution (j : Fin 2) (x y : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    rowM j (x - y) = rowM j x - rowM j y := rfl
end GlobalTheory.Phase.Doubling
