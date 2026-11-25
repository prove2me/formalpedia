-- Prove2me | solution 1 for GlobalTheory.isIntegral_modularJ_of_sq_eq_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T07:04:00.856413+00:00
-- url     : https://prove2.me/submissions/90f346fd-dea1-4890-97b4-14d59bb6fcf2

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
theorem _root_.solution {w : ℍ} {d : ℤ} (h : (2 * (w : ℂ) - 1) ^ 2 = -d) :
    IsIntegral ℤ (modularJ w) :=
  isIntegral_modularJ_of_quadratic (a := 4) (b := -4) (c := 1 + d) (by norm_num)
    (by push_cast; linear_combination h)
end GlobalTheory
