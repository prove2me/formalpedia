-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.norm_prinSymb_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T03:22:08.546735+00:00
-- url     : https://prove2.me/submissions/53931077-6a48-48e0-be10-71e17ecd6c0b

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_SobolevMultiplication
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators

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
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) (ξ : E) :
    ‖prinSymb c w ξ‖ ≤ (∑ i, ‖c i‖ * ∏ j, ‖w i j‖) * ‖ξ‖ ^ m := by
  rw [prinSymb, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ ↦ ?_)
  rw [norm_mul, norm_prod, mul_assoc, ← Fin.prod_const m ‖ξ‖, ← Finset.prod_mul_distrib]
  gcongr with j
  rw [Complex.norm_real, Real.norm_eq_abs, mul_comm]
  exact abs_real_inner_le_norm ξ (w i j)
end GroundTheory.Automorphic.Sobolev
