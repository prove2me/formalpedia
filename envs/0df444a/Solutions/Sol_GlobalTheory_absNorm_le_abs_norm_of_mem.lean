-- Prove2me | solution 1 for GlobalTheory.absNorm_le_abs_norm_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:14:51.041336+00:00
-- url     : https://prove2.me/submissions/bd133691-fabd-421b-b545-76ff48040efb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_FinrankMulDiscrRpowLeSumSqOfMemTraceDual

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
open scoped nonZeroDivisors
open GlobalTheory
variable {K : Type*} [Field K] [NumberField K]
namespace GlobalTheory
theorem _root_.solution {J : FractionalIdeal (𝓞 K)⁰ K} {x : K} (hx : x ∈ J)
    (h0 : x ≠ 0) : FractionalIdeal.absNorm J ≤ |Algebra.norm ℚ x| := by
  have hJ : J ≠ 0 := by
    rintro rfl
    exact h0 ((FractionalIdeal.mem_zero_iff _).mp hx)
  have hle : FractionalIdeal.spanSingleton (𝓞 K)⁰ x * J⁻¹ ≤ 1 := by
    calc _ ≤ J * J⁻¹ := by
          gcongr
          exact FractionalIdeal.spanSingleton_le_iff_mem.mpr hx
      _ = 1 := mul_inv_cancel₀ hJ
  obtain ⟨I, hI⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle
  have hI' : FractionalIdeal.spanSingleton (𝓞 K)⁰ x = I * J := by
    rw [hI, inv_mul_cancel_right₀ hJ]
  have hI0 : I ≠ ⊥ := by
    rintro rfl
    exact h0 (FractionalIdeal.spanSingleton_eq_zero_iff.mp (by simpa using hI'))
  have h1 : (1 : ℚ) ≤ Ideal.absNorm I := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI0)
  rw [← FractionalIdeal.absNorm_span_singleton (𝓞 K), hI', map_mul,
    FractionalIdeal.coeIdeal_absNorm]
  exact le_mul_of_one_le_left (FractionalIdeal.absNorm_nonneg _) h1
end GlobalTheory
