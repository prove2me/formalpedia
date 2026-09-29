-- Prove2me | solution 1 for ModularCurve.hasSum_cosetSubst_coeff_mul_qParam_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/1d1c69dd-776d-51f7-99ff-42f2026b8911

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PrimCosetReps
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow

set_option autoImplicit false

noncomputable section

p2m_open "ModularCurve P2MW.S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow.ModularCurve Complex"

namespace ModularCurve
p2m_export "ModularCurve" "qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd qTwist qTwist_coeff cosetSubst"
namespace CosetQParamAux
p2m_open "ModularCurve"

theorem qParam_coset {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N) (τ : ℂ) :
    Function.Periodic.qParam 1 ((a * τ + b) / d)
      = Complex.exp (2 * Real.pi * Complex.I / N) ^ (a * b) * Function.Periodic.qParam N τ ^ (a * a) := by
  have hd0 : (d : ℂ) ≠ 0 := by
    have : d ≠ 0 := by rintro rfl; exact hN (by simpa using had.symm)
    exact_mod_cast this
  have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast hN
  unfold Function.Periodic.qParam
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  have hNad : (N : ℂ) = a * d := by exact_mod_cast had.symm
  have ha0 : (a : ℂ) ≠ 0 := by
    have : a ≠ 0 := by rintro rfl; exact hN (by simpa using had.symm)
    exact_mod_cast this
  push_cast
  rw [hNad]
  field_simp
  ring

end ModularCurve.CosetQParamAux

open ModularCurve.CosetQParamAux UpperHalfPlane in
theorem solution {N a b d : ℕ} (hN : N ≠ 0) (had : a * d = N)
    [NeZero a] (ζ : ℂˣ) (hζ : (ζ : ℂ) = Complex.exp (2 * Real.pi * Complex.I / N))
    (S : LaurentSeries ℂ) (τ : ℂ) (x : ℂ)
    (h : HasSum (fun m : ℤ => S.coeff m * Function.Periodic.qParam 1 ((a * τ + b) / d) ^ m) x) :
    HasSum (fun m : ℤ => (ModularCurve.cosetSubst ζ a b S).coeff m * Function.Periodic.qParam N τ ^ m) x := by
  haveI : NeZero (a * a) := ⟨Nat.mul_ne_zero (NeZero.ne a) (NeZero.ne a)⟩
  set t : ℂ := Function.Periodic.qParam N τ with ht
  set u : ℂˣ := ζ ^ (a * b) with hu
  rw [qParam_coset hN had τ, ← hζ, ← ht] at h

  have hinj : Function.Injective (fun m : ℤ => ((a * a : ℕ) : ℤ) * m) :=
    mul_right_injective₀ (by exact_mod_cast (NeZero.ne (a * a)))
  refine (Function.Injective.hasSum_iff hinj ?_).mp ?_
  · intro k hk
    have hnd : ¬ ((a * a : ℕ) : ℤ) ∣ k := by
      rintro ⟨c, rfl⟩
      exact hk ⟨c, rfl⟩
    show ((qExpand ℂ (a * a)) (qTwist (ζ ^ (a * b)) S)).coeff k * t ^ k = 0
    rw [qExpand_coeff_of_not_dvd (a * a) _ hnd, zero_mul]
  · have hcomp : ((fun m : ℤ => (ModularCurve.cosetSubst ζ a b S).coeff m * t ^ m) ∘
        (fun m : ℤ => ((a * a : ℕ) : ℤ) * m))
        = fun m : ℤ => S.coeff m * ((ζ : ℂ) ^ (a * b) * t ^ (a * a)) ^ m := by
      funext m
      simp only [Function.comp_apply]
      show ((qExpand ℂ (a * a)) (qTwist (ζ ^ (a * b)) S)).coeff (((a * a : ℕ) : ℤ) * m) * t ^ _ = _
      rw [qExpand_coeff_mul, qTwist_coeff, Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val, mul_zpow,
        zpow_mul, zpow_natCast]
      ring
    rw [hcomp]
    exact h

end

end S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow
end P2MW
export P2MW.S_ModularCurve_hasSum_cosetSubst_coeff_mul_qParam_pow (solution)
