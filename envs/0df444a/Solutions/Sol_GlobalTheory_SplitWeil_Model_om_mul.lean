-- Prove2me | solution 1 for GlobalTheory.SplitWeil.Model.om_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:41:04.789282+00:00
-- url     : https://prove2.me/submissions/cb0a039e-62b2-4b30-8c84-7b2514b64db3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_pos
import Theorems.Thm_GlobalTheory_SplitWeil_Model_nabs_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
open scoped NNReal ENNReal Pointwise
noncomputable section
open GlobalTheory GlobalTheory.SplitWeil GlobalTheory.SplitWeil.Model
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.SplitWeil.Model
theorem _root_.solution {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ)
    (g g' : GL a k) (h h' : GL b k) (Φ : Matrix b a k → ℂ) :
    om μ (g * g') (h * h') Φ = om μ g h (om μ g' h' Φ) := by
  funext x
  simp only [om, map_mul, nabs_mul, Real.mul_rpow (nabs_pos _).le (nabs_pos _).le,
    _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc, Complex.ofReal_mul]
  ring
end GlobalTheory.SplitWeil.Model
