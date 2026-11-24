-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.dup_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:19:58.957835+00:00
-- url     : https://prove2.me/submissions/05f8662b-b606-4361-981f-91c08ae4796f

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
theorem _root_.solution (φ : Matrix (Fin n) (Fin g) ℚ → ℂ) (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    dup φ x = φ (rowM 0 x) * φ (rowM 1 x) := rfl
end GlobalTheory.Phase.Doubling
