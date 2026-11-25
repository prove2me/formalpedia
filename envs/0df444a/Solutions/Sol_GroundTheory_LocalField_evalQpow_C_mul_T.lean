-- Prove2me | solution 1 for GroundTheory.LocalField.evalQpow_C_mul_T
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:15:53.208108+00:00
-- url     : https://prove2.me/submissions/bed33c01-3bab-4b05-981b-ec55c39fd2e0

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalZetaChar
import Definitions.Def_GroundTheory_LocalFields_LocalZetaIntegral

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
theorem _root_.solution (a : ℂ) (n : ℤ) (s : ℂ) :
    evalQpow K (LaurentPolynomial.C a * LaurentPolynomial.T n) s =
      a * ((residueCard K : ℂ) ^ (-s)) ^ n := by
  rw [evalQpow, LaurentPolynomial.eval₂_C_mul_T, Units.val_zpow_eq_zpow_val]
  rfl
end GroundTheory.LocalField
