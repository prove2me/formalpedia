-- Prove2me | solution 1 for ModularCurve.coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3de58e66-9cfc-53ac-9ac8-2b213e13ecf7

import Mathlib
import Definitions.Def_ModularCurve_FrobeniusModL
import Definitions.Def_ModularCurve_QExpansionDiff
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_D
import Theorems.Thm_ModularCurve_qExpansionDiffAlong_smul
import Theorems.Thm_ModularCurve_coeffMap_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow

set_option autoImplicit false

open ModularCurve HahnSeries

namespace P2MM2

theorem coeff_thetaL (L : Type*) [Field L] (u : LaurentSeries L) (n : ℤ) :
    (thetaL L u).coeff n = (n : L) * u.coeff n := by
  rw [thetaL_apply, coeff_single_mul, one_mul, LaurentSeries.derivative_apply,
    LaurentSeries.hasseDeriv_coeff]
  have h1 : n - 1 + ((1 : ℕ) : ℤ) = n := by push_cast; ring
  rw [h1, Ring.choose_one_right, ← Int.cast_smul_eq_zsmul L n (u.coeff n), smul_eq_mul]

theorem intCast_frobenius (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p] (n : ℤ) :
    frobenius L p (n : L) = (n : L) := by
  have h : (frobenius L p).comp (Int.castRingHom L) = Int.castRingHom L := RingHom.ext_int _ _
  exact (RingHom.congr_fun h n :)

theorem coeffMap_frobenius_thetaL (L : Type*) [Field L] (p : ℕ) [Fact p.Prime] [CharP L p]
    (u : LaurentSeries L) :
    coeffMap (frobenius L p) (thetaL L u) = thetaL L (coeffMap (frobenius L p) u) := by
  ext n
  rw [coeffMap_coeff, coeff_thetaL, coeff_thetaL, coeffMap_coeff, map_mul, intCast_frobenius]

theorem coeff_qexp_dlog_eq_pow_of_eq_coeffMap
    (K : Type*) [Field K] (ℓ : ℕ) [Fact ℓ.Prime] [CharP K ℓ]
    {F : Type*} [Field F] [Algebra K F] (σ : F →ₐ[K] LaurentSeries K)
    (f y : F) (hts : σ y = coeffMap (frobenius K ℓ) (σ f)) (n : ℤ) :
    (qExpansionDiffAlong σ (y⁻¹ • KaehlerDifferential.D K F y)).coeff n =
      ((qExpansionDiffAlong σ (f⁻¹ • KaehlerDifferential.D K F f)).coeff n) ^ ℓ := by
  rw [qExpansionDiffAlong_smul, qExpansionDiffAlong_D, qExpansionDiffAlong_smul,
    qExpansionDiffAlong_D, map_inv₀, map_inv₀, hts, ← coeffMap_frobenius_thetaL, ← map_inv₀,
    ← map_mul, coeffMap_coeff, frobenius_def]

theorem val_eq_coeffMap_of_frobeniusModL_eq_pow
    (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (f y : modularFunctionFieldFullC K N) (hy : frobeniusModL K N ℓ y = f ^ ℓ) :
    (modularFunctionFieldFullC K N).val y =
      coeffMap (frobenius K ℓ) ((modularFunctionFieldFullC K N).val f) := by
  apply qExpand_injective ℓ
  have h1 : ((frobeniusModL K N ℓ y : modularFunctionFieldFullC K N) : LaurentSeries K) =
      ((f ^ ℓ : modularFunctionFieldFullC K N) : LaurentSeries K) := congrArg Subtype.val hy
  rw [coe_frobeniusModL] at h1
  have h2 : ((f ^ ℓ : modularFunctionFieldFullC K N) : LaurentSeries K) =
      ((f : modularFunctionFieldFullC K N) : LaurentSeries K) ^ ℓ :=
    map_pow (modularFunctionFieldFullC K N).val f ℓ
  rw [h2, pow_char_eq_coeffMap_frobenius_qExpand ℓ ((f : modularFunctionFieldFullC K N) : LaurentSeries K),
    coeffMap_qExpand] at h1
  exact h1

end P2MM2

open P2MM2 in
set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (K : Type*) [Field K] {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ] (N : ℕ) [NeZero N]
    (f y : modularFunctionFieldFullC K N) (hy : frobeniusModL K N ℓ y = f ^ ℓ) (n : ℤ) :
    (qExpansionDiffAlong (modularFunctionFieldFullC K N).val
        (y⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) y)).coeff n =
      ((qExpansionDiffAlong (modularFunctionFieldFullC K N).val
        (f⁻¹ • KaehlerDifferential.D K (modularFunctionFieldFullC K N) f)).coeff n) ^ ℓ := by
  exact coeff_qexp_dlog_eq_pow_of_eq_coeffMap K ℓ ((modularFunctionFieldFullC K N).val) f y
    (val_eq_coeffMap_of_frobeniusModL_eq_pow K N f y hy) n

end S_ModularCurve_coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow
end P2MW
export P2MW.S_ModularCurve_coeff_qExpansionDiffAlong_dlog_of_frobeniusModL_eq_pow (solution)
