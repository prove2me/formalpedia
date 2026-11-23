-- Prove2me | solution 1 for GlobalTheory.RootEx.BlockLevi.blockTriangular_inv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:38.784074+00:00
-- url     : https://prove2.me/submissions/9548a5dc-cada-4dd8-ae44-a02ebe8e47ea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DiagPartMulDiagPart

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.BlockLevi
variable {k : Type*} [Field k] {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.RootEx.BlockLevi
theorem _root_.solution (f : ι → ℕ) (b : GL ι k) (hb : b.val.BlockTriangular f) :
    (b⁻¹).val.BlockTriangular f := by
  letI : Invertible b.val := b.invertible
  rw [Matrix.coe_units_inv]
  exact Matrix.blockTriangular_inv_of_blockTriangular hb
end GlobalTheory.RootEx.BlockLevi
