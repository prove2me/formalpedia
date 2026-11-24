-- Prove2me | solution 1 for GlobalTheory.mdifferentiable_modularJ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:20:00.418068+00:00
-- url     : https://prove2.me/submissions/aea1ce71-5595-41a2-b3b1-39e3cae29219

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Theorems.Thm_GlobalTheory_HasQExpansion_pow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real ArithmeticFunction.sigma
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
namespace GlobalTheory
theorem _root_.solution : MDiff modularJ :=
  (E₄.holo'.pow 3).div CuspForm.discriminant.holo' discriminant_ne_zero
end GlobalTheory
