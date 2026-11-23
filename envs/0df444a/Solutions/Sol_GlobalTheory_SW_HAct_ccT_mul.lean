-- Prove2me | solution 1 for GlobalTheory.SW.HAct.ccT_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:50:54.166485+00:00
-- url     : https://prove2.me/submissions/2663f4c0-04e8-4d7f-98a8-d28489807501

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IsHeatZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_UnitaryActHalfSpace

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
open GlobalTheory GlobalTheory.SW GlobalTheory.SW.HAct
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
namespace GlobalTheory.SW.HAct
theorem _root_.solution {α β δ : Type} [Fintype β] (X : Matrix α β E) (Y : Matrix β δ E) :
    ccT (X * Y) = ccT Y * ccT X := by
  ext i j
  simp [ccT, cc, Matrix.mul_apply, mul_comm]
end GlobalTheory.SW.HAct
