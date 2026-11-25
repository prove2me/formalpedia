-- Prove2me | solution 1 for GroundTheory.LocalField.ofReal_modulus_inv_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:47:26.353074+00:00
-- url     : https://prove2.me/submissions/8114a3f7-b31e-4db5-8038-e122ef296fb9

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaGauss
import Definitions.Def_GroundTheory_LocalFields_LocalZeta
import Theorems.Thm_GroundTheory_LocalField_modulus_of_ne_zero
import Theorems.Thm_GroundTheory_LocalField_ofReal_qzpow


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel MeasureTheory Measure Topology Filter
open scoped WithZero NNReal ENNReal Pointwise
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
namespace GroundTheory.LocalField
theorem _root_.solution (a : Kˣ) :
    ((((modulus (a : K) : ℝ))⁻¹ : ℝ) : ℂ) = (residueCard K : ℂ) ^ ((ord (a : K) : ℤ) : ℂ) := by
  rw [modulus_of_ne_zero a.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast, ← zpow_neg, neg_neg,
    ofReal_qzpow]
end GroundTheory.LocalField
