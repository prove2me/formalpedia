-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.opBound_Rop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:10:50.347915+00:00
-- url     : https://prove2.me/submissions/87dca8c4-e940-41e8-bbb9-615158a54495

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rNSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rNSymb_bound
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
theorem _root_.solution {μ : ℝ} (hμ : 0 < μ) (k : ℕ) (s : ℝ) :
    OpBound (Rop a w x₀ μ k) s (s + (2 * m * k : ℕ)) ((4 ^ m * (1 + (μ * cl ^ 2)⁻¹)) ^ k) :=
  opBound_fourierMultiplier (rNSymb_hasTemperateGrowth _ w μ k) fun ξ ↦ by
    rw [show (s - (s + ((2 * m * k : ℕ) : ℝ))) / 2 = -((2 * m * k : ℕ) : ℝ) / 2 by ring]
    exact rNSymb_bound _ w hcl hCu hlow hup hμ k ξ
end GroundTheory.Automorphic.Sobolev
