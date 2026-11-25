-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.opBound_iteratedLineDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:33:58.553833+00:00
-- url     : https://prove2.me/submissions/f0862140-1698-4189-a79e-5d839f05ff3d

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_le_sqrt_one_add_norm_sq
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rpow_eq_sqrt_pow
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_derivSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_iteratedLineDeriv_eq_fourierMultiplier
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_derivSymb_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_sob_fourierMultiplier_le


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
theorem _root_.solution {k : ℕ} (w : Fin k → E) (s : ℝ) :
    OpBound (iteratedLineDerivOpCLM ℂ 𝓢'(E, ℂ) w) s (s - k) (∏ j, (2 * Real.pi * ‖w j‖)) := by
  intro u hu
  rw [iteratedLineDerivOpCLM_apply, iteratedLineDeriv_eq_fourierMultiplier]
  refine sob_fourierMultiplier_le (derivSymb_hasTemperateGrowth w) (fun ξ ↦ ?_) hu
  rw [show (s - (s - k)) / 2 = (k : ℝ) / 2 by ring, rpow_eq_sqrt_pow]
  refine (norm_derivSymb_le w ξ).trans ?_
  gcongr
  exact norm_le_sqrt_one_add_norm_sq ξ
end GroundTheory.Automorphic.Sobolev
