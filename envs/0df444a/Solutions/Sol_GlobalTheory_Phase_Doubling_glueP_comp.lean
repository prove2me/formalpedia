-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.glueP_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:58.98569+00:00
-- url     : https://prove2.me/submissions/809aa3f7-b6c0-4b12-b32d-d184cec31f4e

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
theorem _root_.solution (y : Matrix (Fin 2) (Fin n × Fin g) ℚ × Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    glueP (comp 0 y, comp 1 y) = y := by
  show (glue (rowM 0 y.1) (rowM 1 y.1), glue (rowM 0 y.2) (rowM 1 y.2)) = y
  simp [glue_rowM]
end GlobalTheory.Phase.Doubling
