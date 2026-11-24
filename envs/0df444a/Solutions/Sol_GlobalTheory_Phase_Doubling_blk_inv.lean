-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.blk_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:38:51.896715+00:00
-- url     : https://prove2.me/submissions/c4ecf111-7523-497b-8081-2d677f9f52c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
import Theorems.Thm_GlobalTheory_Phase_Doubling_blk_eq

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
theorem _root_.solution (τ : Matrix (Fin g) (Fin g) ℂ) :
    ((blk n τ).map fun z => (z.im : ℂ))⁻¹ = blk n ((τ.map fun z => (z.im : ℂ))⁻¹) := by
  have : ((blk n τ).map fun z => (z.im : ℂ)) = blk n (τ.map fun z => (z.im : ℂ)) := by
    ext p q
    by_cases h : p.1 = q.1 <;> simp [blk, h]
  rw [this, blk_eq, blk_eq, Matrix.inv_kronecker, inv_one]
end GlobalTheory.Phase.Doubling
