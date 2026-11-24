-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.blk_siegel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:25:56.157807+00:00
-- url     : https://prove2.me/submissions/d1335c77-59b2-475a-803f-30e99dfd61ef

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
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (h : τ ∈ Siegel (Fin g)) :
    blk n τ ∈ Siegel (Fin n × Fin g) := by
  refine ⟨?_, ?_⟩
  · ext p q
    have := h.1.apply p.2 q.2
    by_cases hpq : p.1 = q.1
    · simp [blk, hpq, this]
    · simp [blk, hpq, Ne.symm hpq]
  · have : (blk n τ).map Complex.im = (1 : Matrix (Fin n) (Fin n) ℝ) ⊗ₖ (τ.map Complex.im) := by
      ext p q
      by_cases h : p.1 = q.1 <;> simp [blk, h, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [this]
    exact Matrix.PosDef.one.kronecker h.2
end GlobalTheory.Phase.Doubling
