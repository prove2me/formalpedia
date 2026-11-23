-- Prove2me | solution 1 for GlobalTheory.SW.LinChange.intM_nat_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:58.466791+00:00
-- url     : https://prove2.me/submissions/3742366d-0efb-4320-add5-f943a0ff4cc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.LinChange
variable {K : Type} [Field K] [NumberField K] {κ ι : Type} [Fintype κ] [Fintype ι]
namespace GlobalTheory.SW.LinChange
theorem _root_.solution (M : ℕ) {x : Matrix κ ι K} (hx : IntM x) : IntM ((M : K) • x) :=
  fun k i => by
    rw [Matrix.smul_apply, smul_eq_mul]
    exact (isIntegral_natCast M).mul (hx k i)
end GlobalTheory.SW.LinChange
