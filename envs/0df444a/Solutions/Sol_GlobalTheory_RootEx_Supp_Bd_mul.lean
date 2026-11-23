-- Prove2me | solution 1 for GlobalTheory.RootEx.Supp.Bd.mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:51:25.82681+00:00
-- url     : https://prove2.me/submissions/ee0d941d-6b4c-4c65-a8d2-4dbfa4530b7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_IwasawaBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_CharEqOneOfOpENeZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open scoped Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.Supp
variable {k : Type} [Field k] [ValuativeRel k]
namespace GlobalTheory.RootEx.Supp
namespace Bd
theorem _root_.solution {ι κ τ : Type} [Fintype κ] {γ δ : ValueGroupWithZero k} {x : Matrix ι κ k} {y : Matrix κ τ k}
    (hx : Bd γ x) (hy : Bd δ y) : Bd (γ * δ) (x * y) := by
  intro r s
  rw [Matrix.mul_apply]
  refine Valuation.map_sum_le _ fun t _ => ?_
  rw [map_mul]
  exact mul_le_mul' (hx r t) (hy t s)
end Bd
end GlobalTheory.RootEx.Supp
