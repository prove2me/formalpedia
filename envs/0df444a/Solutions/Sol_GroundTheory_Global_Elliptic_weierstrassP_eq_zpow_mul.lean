-- Prove2me | solution 1 for GroundTheory.Global.Elliptic.weierstrassP_eq_zpow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:07:19.981952+00:00
-- url     : https://prove2.me/submissions/012bafcb-4d4c-4b3e-8c0f-53b56ddd4f49

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticFunctions
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticConstant
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_EllipticRational

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Complex Filter Topology Set Polynomial
open scoped PeriodPair
noncomputable section
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Elliptic
variable {L : PeriodPair}
namespace GroundTheory.Global.Elliptic
theorem _root_.solution {z : ℂ} (hz : z ≠ 0) :
    ℘[L] z = z ^ (-2 : ℤ) * (z ^ 2 * L.weierstrassPExcept 0 z + 1) := by
  have h := L.ite_eq_one_sub_sq_mul_weierstrassP 0 L.lattice.zero_mem z
  rw [if_neg hz] at h
  have h' : z ^ 2 * ℘[L] z = z ^ 2 * L.weierstrassPExcept 0 z + 1 := by
    simpa using h
  have h2 : z ^ (-2 : ℤ) * z ^ 2 = 1 := by
    rw [zpow_neg, zpow_ofNat, inv_mul_cancel₀ (pow_ne_zero 2 hz)]
  rw [← h', ← mul_assoc, h2, one_mul]
end GroundTheory.Global.Elliptic
