-- Prove2me | solution 1 for GlobalTheory.rootNumber_ne_zero_of_isPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:32:48.290936+00:00
-- url     : https://prove2.me/submissions/a4ae99b2-748e-4676-80aa-7cb15eaef97b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_CompletedLFunctionNeZeroOfReNonpos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ.IsPrimitive) : rootNumber χ ≠ 0 := by
  have hG : gaussSum χ ZMod.stdAddChar ≠ 0 := by
    intro h
    have h1 : ZMod.dft (χ : ZMod q → ℂ) = 0 := by
      funext k
      rw [hχ.fourierTransform_eq_inv_mul_gaussSum k, h, mul_zero]
      rfl
    have h2 := congr_fun (ZMod.dft_dft (χ : ZMod q → ℂ)) (-1)
    rw [h1, _root_.map_zero] at h2
    simp only [Pi.zero_apply, neg_neg, map_one, smul_eq_mul, mul_one] at h2
    exact NeZero.ne q (by exact_mod_cast h2.symm)
  unfold rootNumber
  refine div_ne_zero (div_ne_zero hG (pow_ne_zero _ I_ne_zero)) ?_
  rw [Ne, cpow_eq_zero_iff]
  exact fun h => NeZero.ne q (Nat.cast_eq_zero.mp h.1)
end GlobalTheory
