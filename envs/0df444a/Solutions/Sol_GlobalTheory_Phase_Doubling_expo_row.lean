-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.expo_row
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:58.289551+00:00
-- url     : https://prove2.me/submissions/3af56c30-eba1-438b-8a6f-0a2d675e6c4c

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
theorem _root_.solution (τ : Matrix (Fin g) (Fin g) ℂ) (ζ : Fin 2 → Fin n × Fin g → ℂ) (j : Fin 2)
    (x : Matrix (Fin 2) (Fin n × Fin g) ℚ) :
    qv (x j) ⬝ᵥ blk n τ *ᵥ qv (x j) + 2 * (qv (x j) ⬝ᵥ ζ j) =
      ∑ k, (qv (rowM j x k) ⬝ᵥ τ *ᵥ qv (rowM j x k) +
        2 * (qv (rowM j x k) ⬝ᵥ (fun k i => ζ j (k, i)) k)) := by
  simp [dotProduct, mulVec, qv, rowM, blk, Fintype.sum_prod_type, Finset.sum_add_distrib,
    Finset.mul_sum]
end GlobalTheory.Phase.Doubling
