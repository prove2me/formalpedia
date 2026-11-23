-- Prove2me | solution 1 for GlobalTheory.SplitWeil.om_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:17:23.206906+00:00
-- url     : https://prove2.me/submissions/47f6e701-a7d3-429d-8a02-a68ceecd8acb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PadicIsNonarchimedeanLocalField
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_mul
import Theorems.Thm_GlobalTheory_SplitWeil_nabs_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise Topology
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil
variable (k : Type*) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {k}
variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
namespace GlobalTheory.SplitWeil
theorem _root_.solution (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ) := by
  funext x
  simp only [om, map_mul, nabs_mul, Real.mul_rpow (nabs_pos k _).le (nabs_pos k _).le,
    _root_.mul_inv_rev, Units.val_mul, Complex.ofReal_mul, Matrix.mul_assoc]
  ring
end GlobalTheory.SplitWeil
