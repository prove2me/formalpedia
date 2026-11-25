-- Prove2me | solution 1 for GlobalTheory.isIntegral_modularJ_halfOneAddSqrtNeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:18:47.817462+00:00
-- url     : https://prove2.me/submissions/54da741d-722e-4abd-ab96-de9495214340

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_isIntegral_modularJ_of_quadratic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
namespace GlobalTheory
theorem _root_.solution (d : ℕ) (hd : d ≠ 0) :
    IsIntegral ℤ (modularJ (halfOneAddSqrtNeg d hd)) := by
  refine isIntegral_modularJ_of_quadratic (a := 4) (b := -4) (c := 1 + d) (by norm_num) ?_
  have h1 : ((√d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]; simp
  change _ * ((1 + √d * Complex.I) / 2 : ℂ) ^ 2 + _ * ((1 + √d * Complex.I) / 2 : ℂ) + _ = 0
  push_cast
  linear_combination ((√d : ℝ) : ℂ) ^ 2 * Complex.I_sq - h1
end GlobalTheory
