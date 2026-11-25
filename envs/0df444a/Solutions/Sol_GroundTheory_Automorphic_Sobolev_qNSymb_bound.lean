-- Prove2me | solution 1 for GroundTheory.Automorphic.Sobolev.qNSymb_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:42:04.00996+00:00
-- url     : https://prove2.me/submissions/188f676f-45bd-46fe-a0a4-ac6d53c018c7

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticOperators
import Definitions.Def_GroundTheory_AutomorphicForms_PartialDifferential_EllipticLocal
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_le_of_mul_sqrt_pow_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_norm_qNSymb_le
import Theorems.Thm_GroundTheory_Automorphic_Sobolev_qSymb_mul_sqrt_pow_le

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
theorem _root_.solution {μ : ℝ} (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1) (N : ℕ) (ξ : E) :
    ‖qNSymb c w μ N ξ‖ ≤ (N * (2 ^ m * (cl⁻¹ + Cu))) * (1 + ‖ξ‖ ^ 2) ^ (-(m : ℝ) / 2) := by
  refine norm_le_of_mul_sqrt_pow_le (fun ξ ↦ ?_) ξ
  calc ‖qNSymb c w μ N ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m
      ≤ (N * ‖qSymb c w μ ξ‖) * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m := by
        gcongr; exact norm_qNSymb_le c w hμ0 N ξ
    _ = N * (‖qSymb c w μ ξ‖ * Real.sqrt (1 + ‖ξ‖ ^ 2) ^ m) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (qSymb_mul_sqrt_pow_le c w hcl hCu hlow hup hμ0 hμ1 ξ)
        (Nat.cast_nonneg N)
end GroundTheory.Automorphic.Sobolev
