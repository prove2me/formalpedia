-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.comp_glueP_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:57.531231+00:00
-- url     : https://prove2.me/submissions/c50823e7-cf7e-41d3-b587-6f351d73bcf0

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
theorem _root_.solution (a b : Matrix (Fin n) (Fin g) ℚ × Matrix (Fin n) (Fin g) ℚ) :
    comp 0 (glueP (a, b)) = a := by
  show (rowM 0 (glue a.1 b.1), rowM 0 (glue a.2 b.2)) = a
  simp [rowM_glue_zero]
end GlobalTheory.Phase.Doubling
