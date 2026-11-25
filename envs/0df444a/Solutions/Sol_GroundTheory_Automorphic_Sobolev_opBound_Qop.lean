-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.opBound_Qop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:43:06.990546+00:00
-- url     : https://prove2.me/submissions/e62de86c-0483-4dfe-a8e6-2b5c6455c85f

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_qNSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_qNSymb_bound
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_opBound_fourierMultiplier

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
variable {m n : ℕ} (a : Fin n → 𝓢(E, ℂ)) (w : Fin n → Fin m → E) (x₀ : E)
variable {cl Cu : ℝ} (hcl : 0 < cl) (hCu : 0 ≤ Cu)
  (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 (fun i ↦ a i x₀) w ξ‖)
  (hup : ∀ ξ, ‖symb0 (fun i ↦ a i x₀) w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (k : ℕ) (s : ℝ) :
    OpBound (Qop a w x₀ μ k) (s - m) s (k * (2 ^ m * (cl⁻¹ + Cu))) :=
  opBound_fourierMultiplier (qNSymb_hasTemperateGrowth _ w μ k) fun ξ ↦ by
    rw [show (s - m - s) / 2 = -(m : ℝ) / 2 by ring]
    exact qNSymb_bound _ w hcl hCu hlow hup hμ0 hμ1 k ξ
end GroundTheory.Automorphic.Sobolev
