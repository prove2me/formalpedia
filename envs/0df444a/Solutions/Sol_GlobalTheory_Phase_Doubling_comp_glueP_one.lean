-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.comp_glueP_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:56.96851+00:00
-- url     : https://prove2.me/submissions/14a6400a-21a3-4798-8bf4-eafe795fb21f

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
    comp 1 (glueP (a, b)) = b := by
  show (rowM 1 (glue a.1 b.1), rowM 1 (glue a.2 b.2)) = b
  simp [rowM_glue_one]
end GlobalTheory.Phase.Doubling
