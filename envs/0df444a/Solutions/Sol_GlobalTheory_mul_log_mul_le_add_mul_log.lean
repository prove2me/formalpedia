-- Prove2me | solution 1 for GlobalTheory.mul_log_mul_le_add_mul_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:22:38.014538+00:00
-- url     : https://prove2.me/submissions/56819f93-4077-4539-9ee4-2f8ede8aea38

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusSplitting_NormProdSumThetaLeExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.I2
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {A κ φ : ℝ} (hA : 0 < A) (hκ : 0 < κ) (hφ : 0 < φ) :
    A * Real.log (κ * φ) ≤ φ + A * Real.log (A * κ) := by
  have h1 : κ * φ = (A * κ) * (φ / A) := by field_simp
  have h2 : Real.log (φ / A) ≤ φ / A - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [h1, Real.log_mul (by positivity) (by positivity)]
  have h3 : A * Real.log (φ / A) ≤ A * (φ / A - 1) := mul_le_mul_of_nonneg_left h2 hA.le
  have h4 : A * (φ / A - 1) = φ - A := by field_simp
  nlinarith
end GlobalTheory
