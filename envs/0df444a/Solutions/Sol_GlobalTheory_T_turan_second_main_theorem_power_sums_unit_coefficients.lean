-- Prove2me | solution 1 for GlobalTheory.T.turan_second_main_theorem_power_sums_unit_coefficients
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:10.691477+00:00
-- url     : https://prove2.me/submissions/ab9aeffb-aeb4-4b35-a235-b89c154c8c3b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficients
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_TuranSecondMainTheoremPowerSumsUnitCoefficientsStatement
import Theorems.Thm_GlobalTheory_powerSum_second_main


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∃ C : ℝ, 1 ≤ C ∧ ∀ (N M : ℕ) (z : Fin N → ℂ) (i₀ : Fin N), ∃ k : ℕ, M + 1 ≤ k ∧ k ≤ M + N ∧ ((N : ℝ) / (C * (M + N))) ^ N * ‖z i₀‖ ^ k ≤ ‖∑ i, z i ^ k‖ := by
  first | exact @GlobalTheory.powerSum_second_main | exact GlobalTheory.powerSum_second_main | (intros; apply GlobalTheory.powerSum_second_main <;> assumption)
end _root_.GlobalTheory.T
