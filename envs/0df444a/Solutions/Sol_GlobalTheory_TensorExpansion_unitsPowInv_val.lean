-- Prove2me | solution 1 for GlobalTheory.TensorExpansion.unitsPowInv_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:56.58471+00:00
-- url     : https://prove2.me/submissions/2b441fdf-c3ae-49d8-a6e9-bc76967ab56c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
noncomputable section
open GlobalTheory GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace GlobalTheory.TensorExpansion
theorem _root_.solution (ϖ : kˣ) (e : ℕ) : (((ϖ ^ e)⁻¹ : kˣ) : k) = ((ϖ : k) ^ e)⁻¹ := by
  simp [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
end GlobalTheory.TensorExpansion
