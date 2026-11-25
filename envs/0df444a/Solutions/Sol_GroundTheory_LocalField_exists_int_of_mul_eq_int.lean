-- Prove2me | solution 1 for GroundTheory.LocalField.exists_int_of_mul_eq_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:59:54.782486+00:00
-- url     : https://prove2.me/submissions/1c8de211-4c33-4efa-bc25-5ab8e42f277a

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionIntegral
import Theorems.Thm_GroundTheory_LocalField_exists_retraction_adjoin

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
open Module Representation
namespace GroundTheory.LocalField
theorem _root_.solution {ζ : ℂ} (hζ : IsIntegral ℤ ζ) {a : ℂ}
    (ha : a ∈ Algebra.adjoin ℤ ({ζ} : Set ℂ)) {d k : ℤ} (hd : d ≠ 0) (h : (d : ℂ) * a = k) :
    ∃ z : ℤ, a = z ∧ d * z = k := by
  obtain ⟨π, hπ⟩ := exists_retraction_adjoin hζ
  let a' : Algebra.adjoin ℤ ({ζ} : Set ℂ) := ⟨a, ha⟩
  have h' : d • a' = k • (1 : Algebra.adjoin ℤ ({ζ} : Set ℂ)) := by
    apply Subtype.ext
    simp [a', h]
  have h'' := congrArg π h'
  rw [map_zsmul, map_zsmul, hπ, smul_eq_mul, smul_eq_mul, mul_one] at h''
  refine ⟨π a', ?_, h''⟩
  have hd' : (d : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hd
  apply mul_left_cancel₀ hd'
  rw [h, ← h'']
  push_cast
  ring
end GroundTheory.LocalField
