-- Prove2me | solution 1 for GlobalTheory.OppRad.conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:28.874666+00:00
-- url     : https://prove2.me/submissions/0f323308-5ddd-4f70-a1e2-b96564312d2e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MatrixRegular
import Theorems.Thm_GlobalTheory_OppRad_mem_U

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.OppRad
open scoped Classical
variable {R : Type} [Ring R]
namespace GlobalTheory.OppRad
theorem _root_.solution {p q p' q' : R} {w u : Rˣ} (hp : w.val * p' = p * w.val) (hq : w.val * q' = q * w.val)
    (hu : u ∈ U p' q') : w * u * w⁻¹ ∈ U p q := by
  have e : (w * u * w⁻¹).val - 1 = w.val * (u.val - 1) * (w⁻¹).val := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]; rfl
  have hq' : (w⁻¹).val * q = q' * (w⁻¹).val := by
    rw [Units.inv_mul_eq_iff_eq_mul, ← mul_assoc, hq, Units.mul_inv_cancel_right]
  rw [mem_U, e]
  constructor
  · rw [← mul_assoc, ← mul_assoc, ← hp, mul_assoc w.val, hu.1]
  · rw [mul_assoc _ _ q, hq', ← mul_assoc, mul_assoc w.val, hu.2]
end GlobalTheory.OppRad
