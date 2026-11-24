-- Prove2me | solution 1 for GlobalTheory.Hk.RealZero.le_order
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:20:46.025721+00:00
-- url     : https://prove2.me/submissions/ac8b58c1-f311-4cf1-8805-e8b65092fde7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyLogDerivPositivityStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionUniqueSimpleExceptionalZero
import Theorems.Thm_GlobalTheory_Hk_RealZero_order_ne_top
import Theorems.Thm_GlobalTheory_T_rayClassLFunctionFamily_continuation_growth


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ArithmeticFunction MeasureTheory Filter Topology NumberField GlobalTheory.Hk GlobalTheory.Mem
open scoped Classical
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.RealZero
namespace GlobalTheory.Hk.RealZero
theorem _root_.solution (𝓕 : LFam) (χ : AddChar 𝓕.G ℂ) {z : ℂ} (hz : 1 / 2 < z.re) (n : ℕ)
    (hn : ∀ i < n, iteratedDeriv i (𝓕.F χ) z = 0) :
    n ≤ analyticOrderNatAt (𝓕.F χ) z := by
  have hA := (GlobalTheory.T.rayClassLFunctionFamily_continuation_growth 𝓕 χ).1 z hz
  have h := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hA).mpr hn
  rw [← Nat.cast_analyticOrderNatAt (order_ne_top 𝓕 χ hz)] at h
  exact_mod_cast h
end GlobalTheory.Hk.RealZero
