-- Prove2me | solution 1 for GlobalTheory.ZModPerp.dvd_of_forall_mul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:17:58.868465+00:00
-- url     : https://prove2.me/submissions/53dfc148-6f6c-4bdd-beed-db350942217a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_OrthogonalFreeOfPerfectAltZmod
import Theorems.Thm_GlobalTheory_ZModPerp_exists_eq_nsmul_zmod

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
theorem _root_.solution {n : ℕ} [NeZero n] (x y : ZMod n)
    (h : ∀ a : ZMod n, a * x = 0 → a * y = 0) : x ∣ y := by
  obtain ⟨m, hm⟩ := Nat.gcd_dvd_right x.val n
  obtain ⟨k, hk⟩ := Nat.gcd_dvd_left x.val n
  have h1 : (m : ZMod n) * x = 0 := by
    have : ((m * x.val : ℕ) : ZMod n) = 0 := by
      rw [ZMod.natCast_eq_zero_iff]
      refine ⟨k, ?_⟩
      calc m * x.val = m * (Nat.gcd x.val n * k) := by rw [← hk]
        _ = (Nat.gcd x.val n * m) * k := by ring
        _ = n * k := by rw [← hm]
    simpa using this
  obtain ⟨z, hz⟩ := exists_eq_nsmul_zmod hm.symm y (by simpa [nsmul_eq_mul] using h _ h1)
  have h2 := congrArg (Int.cast : ℤ → ZMod n) (Nat.gcd_eq_gcd_ab x.val n)
  simp only [Int.cast_natCast, Int.cast_add, Int.cast_mul, ZMod.natCast_self, zero_mul, add_zero,
    ZMod.natCast_zmod_val] at h2
  rw [hz, nsmul_eq_mul, h2, mul_assoc]
  exact dvd_mul_right _ _
end GlobalTheory.ZModPerp
