-- Prove2me | solution 1 for GlobalTheory.T.summable_lipschitzLatticeNormPowSummand
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T21:22:20.915417+00:00
-- url     : https://prove2.me/submissions/be3d8138-2400-4f60-949d-85cb6570855c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RembApply
import Definitions.Def_Formalism_LatticeTheta_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SummableLipschitzLatticeNormPowSummandStatement
import Theorems.Thm_GlobalTheory_LipschitzTR_summable_lhsTerm_ideal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M : FractionalIdeal (𝓞 F)⁰ F), M ≠ 0 → ∀ (k : ℕ), 2 ≤ k → ∀ (z : (F →+* ℝ) → ℂ), (∀ τ, (z τ).im ≠ 0) → Summable (fun a : (M : Set F) => lhsTerm k z a) := by
  first | exact @GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | exact GlobalTheory.LipschitzTR.summable_lhsTerm_ideal | (intros; apply GlobalTheory.LipschitzTR.summable_lhsTerm_ideal <;> assumption)
end _root_.GlobalTheory.T
