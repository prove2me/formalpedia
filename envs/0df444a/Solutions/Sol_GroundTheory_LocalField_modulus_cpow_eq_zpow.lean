-- Prove2me | solution 1 for GroundTheory.LocalField.modulus_cpow_eq_zpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:46:37.270282+00:00
-- url     : https://prove2.me/submissions/ecbd2c14-a672-4b0c-bdf0-6214d0fa8728

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_GroundTheory_LocalFields_LocalZetaShell
import Theorems.Thm_GroundTheory_LocalField_residueCard_pos_real
import Theorems.Thm_GroundTheory_LocalField_residueCard_ne_zero_complex
import Theorems.Thm_GroundTheory_LocalField_modulus_of_ne_zero


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
theorem _root_.solution (u : Kˣ) (s : ℂ) :
    ((modulus (u : K) : ℝ) : ℂ) ^ s = ((residueCard K : ℂ) ^ (-s)) ^ ord (u : K) := by
  have hq := residueCard_pos_real (K := K)
  rw [modulus_of_ne_zero u.ne_zero, NNReal.coe_zpow, NNReal.coe_natCast]
  have hpos : (0 : ℝ) < (residueCard K : ℝ) ^ (-ord (u : K)) := zpow_pos hq _
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hpos.ne'),
    Complex.cpow_def_of_ne_zero residueCard_ne_zero_complex, ← Complex.exp_int_mul,
    ← Complex.ofReal_log hpos.le, Real.log_zpow, ← Complex.ofReal_natCast,
    ← Complex.ofReal_log hq.le]
  push_cast
  ring_nf
end GroundTheory.LocalField
