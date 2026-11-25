-- Prove2me | solution 1 for GlobalTheory.T.ray_L_nonvanishing_at_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T01:29:34.013003+00:00
-- url     : https://prove2.me/submissions/c5a2d32e-3730-47f2-bbd4-c03d836487f6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_NonemptyRayDataOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RayLNonvanishingAtOneStatement
import Theorems.Thm_GlobalTheory_Mem_rayLSeries_entire_ne_zero_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → ∀ (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ), χ ≠ 1 → ∃ L : ℂ → ℂ, Differentiable ℂ L ∧ L 1 ≠ 0 ∧ ∀ s : ℂ, 1 < s.re → L s = LSeries (D.coef χ) s := by
  first | exact @GlobalTheory.Mem.rayLSeries_entire_ne_zero_one | exact GlobalTheory.Mem.rayLSeries_entire_ne_zero_one | (intros; apply GlobalTheory.Mem.rayLSeries_entire_ne_zero_one <;> assumption)
end _root_.GlobalTheory.T
