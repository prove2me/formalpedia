-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.rNSymb_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T07:17:56.685733+00:00
-- url     : https://prove2.me/submissions/c34ebc8b-19bc-4ea5-8c0d-3c2e3afcb92c

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_le_of_mul_sqrt_pow_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_rhoSymb_mul_sqrt_pow_le

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
variable {ι : Type*} [Fintype ι] {m : ℕ} (c : ι → ℂ) (w : ι → Fin m → E) {cl Cu : ℝ}
variable (hcl : 0 < cl) (hCu : 0 ≤ Cu) (hlow : ∀ ξ, cl * ‖ξ‖ ^ m ≤ ‖symb0 c w ξ‖)
  (hup : ∀ ξ, ‖symb0 c w ξ‖ ≤ Cu * ‖ξ‖ ^ m)
include hcl hCu hlow hup
namespace GroundTheory.Automorphic.Sobolev
theorem _root_.solution {μ : ℝ} (hμ : 0 < μ) (N : ℕ) (ξ : E) :
    ‖rNSymb c w μ N ξ‖ ≤ (4 ^ m * (1 + (μ * cl ^ 2)⁻¹)) ^ N *
      (1 + ‖ξ‖ ^ 2) ^ (-((2 * m * N : ℕ) : ℝ) / 2) := by
  refine norm_le_of_mul_sqrt_pow_le (fun ξ ↦ ?_) ξ
  rw [rNSymb, norm_pow, show 2 * m * N = (2 * m) * N by ring, pow_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (rhoSymb_mul_sqrt_pow_le c w hcl hCu hlow hup hμ ξ) N
end GroundTheory.Automorphic.Sobolev
