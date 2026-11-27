-- Prove2me | solution 1 for GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:41:48.665102+00:00
-- url     : https://prove2.me/submissions/a1a400c1-81ce-44fa-9f27-434e6d8292c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteCoeffTendstoAndBounded
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteCoeffTendstoAndBoundedStatement
import Theorems.Thm_GlobalTheory_JacobiTriple_finCoeff_tendsto_and_bounded


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ t : ℂ, ‖t‖ < 1 → (∀ j : ℤ, Filter.Tendsto (fun n : ℕ => GlobalTheory.JacobiTriple.finCoeff t n j) Filter.atTop (nhds (GlobalTheory.JacobiTriple.qPochInf t)⁻¹)) ∧ ∃ C : ℝ, ∀ (n : ℕ) (j : ℤ), ‖GlobalTheory.JacobiTriple.finCoeff t n j‖ ≤ C := by
  first | exact @GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded | exact GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded | (intros; apply GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded <;> assumption)
end _root_.GlobalTheory.T
