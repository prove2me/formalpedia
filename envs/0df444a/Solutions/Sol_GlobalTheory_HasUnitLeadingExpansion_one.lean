-- Prove2me | solution 1 for GlobalTheory.HasUnitLeadingExpansion.one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:21:27.579797+00:00
-- url     : https://prove2.me/submissions/a751090e-3992-4607-8d04-1eab6fa1bd77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_HasQExpansion_const


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
namespace HasUnitLeadingExpansion
theorem _root_.solution (n : ℝ) : HasUnitLeadingExpansion n 1 :=
  ⟨0, 1, one_mem _, by simp, by simpa using isIntegral_one,
    by simpa using HasQExpansion.const n 1⟩
end HasUnitLeadingExpansion
end GlobalTheory
