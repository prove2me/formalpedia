-- Prove2me | solution 1 for GlobalTheory.qParam_one_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:17:18.545396+00:00
-- url     : https://prove2.me/submissions/e8a05925-121e-41e6-b52c-5212bfa74126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsPolynomialModularJOfHasQExpansion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ModularJExpansionAndPolynomialAndIsIntegral
import Theorems.Thm_GlobalTheory_HasQExpansion_congr


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
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (z : ℂ) : 𝕢 1 z = 𝕢 n z ^ n := by
  have : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  field_simp
end GlobalTheory
