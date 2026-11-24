-- Prove2me | solution 1 for GlobalTheory.Hk.LogDerivHalf.sum_le_of_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:47:42.301939+00:00
-- url     : https://prove2.me/submissions/d71bb942-2e09-4807-aa6e-cadf401b7352

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_LamIdealOfNotPrimePow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionFamilyContinuationGrowthStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassFamilyLogDerivReGtOneStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_RayClassLFunctionLogDerivLocalFormulaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivSubExceptionalLe

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
open GlobalTheory GlobalTheory.Hk GlobalTheory.Hk.LogDerivHalf
namespace GlobalTheory.Hk.LogDerivHalf
theorem _root_.solution {ι : Type*} {Z : Finset ι} (hZ : Z.card ≤ 1) {f : ι → ℂ} {M : ℝ} (hM : 0 ≤ M)
    (h : ∀ i ∈ Z, ‖f i‖ ≤ M) : ‖∑ i ∈ Z, f i‖ ≤ M := by
  rcases Z.eq_empty_or_nonempty with hE | ⟨i, hi⟩
  · simpa [hE] using hM
  · have hZi : Z = {i} := Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hi, fun x hx => Finset.card_le_one.mp hZ x hx i hi⟩
    rw [hZi, Finset.sum_singleton]
    exact h i hi
end GlobalTheory.Hk.LogDerivHalf
