-- Prove2me | solution 1 for GlobalTheory.twelve_dvd_sigma
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:58.009306+00:00
-- url     : https://prove2.me/submissions/702cb6a6-9159-4211-9671-847b64a84694

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion

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
theorem _root_.solution (n : ℕ) : (12 : ℤ) ∣ 5 * (σ 3 n : ℤ) + 7 * (σ 5 n : ℤ) := by
  simp only [ArithmeticFunction.sigma_apply, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.dvd_sum fun d _ ↦ ?_
  have : ∀ x : ZMod 12, 5 * x ^ 3 + 7 * x ^ 5 = 0 := by decide
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ 12).mp
  push_cast
  exact this d
end GlobalTheory
