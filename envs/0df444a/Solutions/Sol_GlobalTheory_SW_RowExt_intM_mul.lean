-- Prove2me | solution 1 for GlobalTheory.SW.RowExt.intM_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:06.009846+00:00
-- url     : https://prove2.me/submissions/5b0965ec-2139-45d1-a69e-f3e4c67fdccb

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
theorem _root_.solution [Fintype β] {A : Matrix α β E} {B : Matrix β γ E} (hA : IntM A) (hB : IntM B) :
    IntM (A * B) := fun a c => by
  rw [Matrix.mul_apply]
  exact IsIntegral.sum _ fun b _ => (hA a b).mul (hB b c)
end GlobalTheory.SW.RowExt
