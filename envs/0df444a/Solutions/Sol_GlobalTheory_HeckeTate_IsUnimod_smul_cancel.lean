-- Prove2me | solution 1 for GlobalTheory.HeckeTate.IsUnimod.smul_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:54:41.757269+00:00
-- url     : https://prove2.me/submissions/4843e814-6008-4fbf-931b-5d4c7c9bf9e9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdMulOfIdem
import Theorems.Thm_GlobalTheory_HeckeTate_IsUnimod_ext

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.HeckeTate
variable {R : Type} [CommRing R] {M M' : Type} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
variable {σ : R ≃+* R} {B : M →+ M →+ ℤ} {B' : M' →+ M' →+ ℤ}
namespace GlobalTheory.HeckeTate
namespace IsUnimod
theorem _root_.solution (h : IsUnimod σ B) {n : ℕ} (hn : n ≠ 0) {x y : M}
    (e : (n : R) • x = (n : R) • y) : x = y := by
  refine h.ext fun a => mul_left_cancel₀ (Int.natCast_ne_zero.2 hn) ?_
  rw [← nsmul_eq_mul, ← nsmul_eq_mul, ← map_nsmul, ← map_nsmul, ← Nat.cast_smul_eq_nsmul R,
    ← Nat.cast_smul_eq_nsmul R, e]
end IsUnimod
end GlobalTheory.HeckeTate
