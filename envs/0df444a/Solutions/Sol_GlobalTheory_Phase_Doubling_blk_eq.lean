-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.blk_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:55.274202+00:00
-- url     : https://prove2.me/submissions/d6af58e1-c25e-4f20-bd24-e99b559ecb7f

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
theorem _root_.solution (τ : Matrix (Fin g) (Fin g) ℂ) : blk n τ = (1 : Matrix (Fin n) (Fin n) ℂ) ⊗ₖ τ := by
  ext p q
  by_cases h : p.1 = q.1 <;> simp [blk, h, Matrix.one_apply, Matrix.kroneckerMap_apply]
end GlobalTheory.Phase.Doubling
