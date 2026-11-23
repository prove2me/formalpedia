-- Prove2me | solution 1 for GlobalTheory.SW.RowExt.intM_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:57:01.199512+00:00
-- url     : https://prove2.me/submissions/796fc30a-601c-4f0c-b70e-6e173915edb3

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
theorem _root_.solution {A : Matrix α β E} (n : ℕ) (hA : IntM A) : IntM ((n : E) • A) := fun a b =>
  (isIntegral_natCast n).mul (hA a b)
end GlobalTheory.SW.RowExt
