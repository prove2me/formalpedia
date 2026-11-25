-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.opBound_Qop_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:24:10.416525+00:00
-- url     : https://prove2.me/submissions/f15b59a5-5b04-4a00-8cc5-d82c4a2a454c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_le_of_mul_sqrt_pow_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_qNSymb_hasTemperateGrowth
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_qNSymb_le
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
theorem _root_.solution (hm : 1 ≤ m) {μ ε : ℝ} (hμ0 : 0 ≤ μ)
    (hsmall : ∀ ξ : E, ‖qSymb (fun i ↦ a i x₀) w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ (m - 1) ≤ ε)
    (k : ℕ) (s : ℝ) : OpBound (Qop a w x₀ μ k) (s - m + 1) s (k * ε) :=
  opBound_fourierMultiplier (qNSymb_hasTemperateGrowth _ w μ k) fun ξ ↦ by
    have h := norm_le_of_mul_sqrt_pow_le hsmall ξ
    rw [show (s - m + 1 - s) / 2 = -((m - 1 : ℕ) : ℝ) / 2 by push_cast [hm]; ring]
    calc ‖qNSymb _ w μ k ξ‖ ≤ k * ‖qSymb (fun i ↦ a i x₀) w μ ξ‖ := norm_qNSymb_le _ w hμ0 k ξ
      _ ≤ k * (ε * (1 + ‖ξ‖ ^ 2) ^ (-((m - 1 : ℕ) : ℝ) / 2)) := by gcongr
      _ = _ := by ring
end GroundTheory.Automorphic.Sobolev
