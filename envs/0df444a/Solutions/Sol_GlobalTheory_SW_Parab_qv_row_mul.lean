-- Prove2me | solution 1 for GlobalTheory.SW.Parab.qv_row_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:05.51017+00:00
-- url     : https://prove2.me/submissions/50898ffb-4f2c-4e7b-8381-cc2f143063ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_RationalSchwartzBruhatAlgebraIntegralLinearStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SchwartzBruhatInvariantIntegralMatrixMulStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.Parab
open Matrix Complex
open scoped ComplexConjugate Real
namespace GlobalTheory.SW.Parab
namespace _root_.GlobalTheory.SW.Parab
theorem _root_.solution {κ ι : Type} [Fintype ι] (x : Matrix κ ι ℚ) (A : Matrix ι ι ℚ) (k : κ) :
    _root_.GlobalTheory.SW.qv ((x * A) k) = _root_.GlobalTheory.SW.qv (x k) ᵥ* _root_.GlobalTheory.SW.qm A := by
  funext j
  simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.qm, vecMul, dotProduct, mul_apply]
end _root_.GlobalTheory.SW.Parab
end GlobalTheory.SW.Parab
