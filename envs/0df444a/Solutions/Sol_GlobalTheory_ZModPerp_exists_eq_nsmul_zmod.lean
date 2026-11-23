-- Prove2me | solution 1 for GlobalTheory.ZModPerp.exists_eq_nsmul_zmod
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:15:45.903321+00:00
-- url     : https://prove2.me/submissions/092460f0-8c5d-43c8-8751-e48645be2c15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_OrthogonalFreeOfPerfectAltZmod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory GlobalTheory.ZModPerp
namespace GlobalTheory.ZModPerp
theorem _root_.solution {n r N : ℕ} [NeZero n] (h : r * N = n) (y : ZMod n)
    (hy : N • y = 0) : ∃ z : ZMod n, y = r • z := by
  have hN : N ≠ 0 := by
    rintro rfl
    exact NeZero.ne n (by simpa using h.symm)
  have h1 : ((N * y.val : ℕ) : ZMod n) = 0 := by
    simpa [nsmul_eq_mul] using hy
  rw [ZMod.natCast_eq_zero_iff] at h1
  replace h1 : N * r ∣ N * y.val := by rwa [mul_comm N r, h]
  obtain ⟨k, hk⟩ := Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hN) h1
  refine ⟨(k : ZMod n), ?_⟩
  rw [← ZMod.natCast_zmod_val y, hk]
  simp [nsmul_eq_mul]
end GlobalTheory.ZModPerp
