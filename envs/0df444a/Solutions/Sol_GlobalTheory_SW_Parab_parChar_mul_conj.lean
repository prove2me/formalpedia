-- Prove2me | solution 1 for GlobalTheory.SW.Parab.parChar_mul_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T20:28:29.123207+00:00
-- url     : https://prove2.me/submissions/a8168e76-f187-4d60-8bd6-b306edc0fb9a

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
theorem _root_.solution {κ ι : Type} [Fintype κ] [Fintype ι]
    (S : Matrix ι ι ℚ) (x : Matrix κ ι ℚ) :
    _root_.GlobalTheory.SW.Parab.parChar S x * conj (_root_.GlobalTheory.SW.Parab.parChar S x) = 1 := by
  unfold _root_.GlobalTheory.SW.Parab.parChar
  rw [← Complex.exp_conj, ← Complex.exp_add]
  convert Complex.exp_zero using 2
  simp [Complex.conj_I, map_ratCast]
end _root_.GlobalTheory.SW.Parab
end GlobalTheory.SW.Parab
