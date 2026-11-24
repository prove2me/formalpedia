-- Prove2me | solution 1 for GlobalTheory.SW.RowExt.intM_J
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:28:29.864301+00:00
-- url     : https://prove2.me/submissions/f62c5f62-3cd9-47a1-8aec-0dfd48ba9df0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_ExistsUnitaryExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.RowExt
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {α β γ : Type}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.SW.RowExt
theorem _root_.solution [DecidableEq α] : IntM (Matrix.J α E) := by
  rintro (a | a) (b | b) <;> by_cases h : a = b <;>
    simp [Matrix.J, Matrix.one_apply, h, isIntegral_zero, isIntegral_one, isIntegral_one.neg]
end GlobalTheory.SW.RowExt
