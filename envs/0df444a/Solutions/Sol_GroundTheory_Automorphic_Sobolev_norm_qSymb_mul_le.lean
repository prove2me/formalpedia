-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_qSymb_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:04:07.64927+00:00
-- url     : https://prove2.me/submissions/02bb4121-ae8c-4833-9fa3-557602bb3ffd

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_qSymb

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Sobolev
open TemperedDistribution MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap ENNReal ContDiff
noncomputable section
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E)
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {μ : ℝ} (hμ : 0 ≤ μ) (ξ : E) :
    ‖qSymb c w μ ξ‖ * ‖symb0 c w ξ‖ ≤ 1 := by
  rw [norm_qSymb c w hμ]
  have hpos : (0 : ℝ) < 1 + μ * ‖symb0 c w ξ‖ ^ 2 := by positivity
  rw [show μ * ‖symb0 c w ξ‖ * (1 + μ * ‖symb0 c w ξ‖ ^ 2)⁻¹ * ‖symb0 c w ξ‖ =
    (μ * ‖symb0 c w ξ‖ ^ 2) / (1 + μ * ‖symb0 c w ξ‖ ^ 2) by field_simp]
  rw [div_le_one hpos]; linarith
end GroundTheory.Automorphic.Sobolev
