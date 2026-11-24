-- Prove2me | solution 1 for GlobalTheory.SW.Parab.qv_bilin
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:17:31.403201+00:00
-- url     : https://prove2.me/submissions/6db8c35f-3e52-490e-9e2b-dbcf1f451daf

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
theorem _root_.solution {ι : Type} [Fintype ι] (S : Matrix ι ι ℚ) (v : ι → ℚ) :
    ((v ⬝ᵥ S *ᵥ v : ℚ) : ℂ) = _root_.GlobalTheory.SW.qv v ⬝ᵥ _root_.GlobalTheory.SW.qm S *ᵥ _root_.GlobalTheory.SW.qv v := by
  simp [_root_.GlobalTheory.SW.qv, _root_.GlobalTheory.SW.qm, mulVec, dotProduct]
end _root_.GlobalTheory.SW.Parab
end GlobalTheory.SW.Parab
