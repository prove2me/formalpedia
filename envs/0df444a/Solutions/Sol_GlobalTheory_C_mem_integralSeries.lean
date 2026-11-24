-- Prove2me | solution 1 for GlobalTheory.C_mem_integralSeries
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:07:03.930122+00:00
-- url     : https://prove2.me/submissions/7d6a706b-4ff4-499c-aa75-3f75b966b2b7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral

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
theorem _root_.solution {c : ℂ} (hc : IsIntegral ℤ c) : C c ∈ integralSeries := fun k ↦ by
  rw [coeff_C]
  split_ifs
  exacts [hc, isIntegral_zero]
end GlobalTheory
