-- Prove2me | solution 1 for GlobalTheory.Phase.Doubling.isSB_dup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:52.736799+00:00
-- url     : https://prove2.me/submissions/c94782ae-115e-45da-874f-e73fe579890f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SummableNormSiegelThetaSeriesTerms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_DoubledRowTestFunctionProperties
import Theorems.Thm_GlobalTheory_Phase_Doubling_dup_apply
import Theorems.Thm_GlobalTheory_Phase_Doubling_rowM_add
import Theorems.Thm_GlobalTheory_Phase_Doubling_rowM_smul

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
theorem _root_.solution {φ : Matrix (Fin n) (Fin g) ℚ → ℂ} (h : IsSB φ) : IsSB (dup φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx j p => ?_, fun x y hy => ?_⟩
  · rw [dup_apply] at hx
    fin_cases j
    · exact h1 _ (left_ne_zero_of_mul hx) p.1 p.2
    · exact h1 _ (right_ne_zero_of_mul hx) p.1 p.2
  · rw [dup_apply, dup_apply, rowM_add, rowM_add, rowM_smul, rowM_smul,
      h2 _ (rowM 0 y) (fun k i => hy 0 (k, i)), h2 _ (rowM 1 y) (fun k i => hy 1 (k, i))]
end GlobalTheory.Phase.Doubling
