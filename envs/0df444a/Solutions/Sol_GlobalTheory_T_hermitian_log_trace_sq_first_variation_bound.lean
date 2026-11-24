-- Prove2me | solution 1 for GlobalTheory.T.hermitian_log_trace_sq_first_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:12:26.577985+00:00
-- url     : https://prove2.me/submissions/b10d5197-6d28-4c25-ab10-d4dd2371a408

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBound
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_HermitianLogTraceSqFirstVariationBoundStatement
import Theorems.Thm_GlobalTheory_ClassFin_LogSqVar_first_variation


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (H A : Matrix ι ι ℂ), IsLog H A → ∃ C δ : ℝ, 0 < δ ∧ ∀ Y H' : Matrix ι ι ℂ, (∀ i j, ‖Y i j‖ ≤ δ) → IsLog H' (A + Y) → (Matrix.trace (H' * H')).re ≤ (Matrix.trace (H * H)).re + 2 * (Matrix.trace (H * A⁻¹ * Y)).re + C * ∑ i, ∑ j, ‖Y i j‖ ^ 2 := by
  first | exact @GlobalTheory.ClassFin.LogSqVar.first_variation | exact GlobalTheory.ClassFin.LogSqVar.first_variation | (intros; apply GlobalTheory.ClassFin.LogSqVar.first_variation <;> assumption)
end _root_.GlobalTheory.T
