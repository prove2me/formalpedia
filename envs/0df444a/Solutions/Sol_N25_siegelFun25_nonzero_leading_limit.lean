-- Prove2me | solution 1 for N25.siegelFun25_nonzero_leading_limit
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:47:49.441114+00:00
-- url     : https://prove2.me/submissions/d720bc11-d347-4ea5-870f-844314e89d39

import Mathlib
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_ModularCurve_SiegelUnit_exists_isIntegral_hasSum_siegelFun
import Theorems.Thm_N25_siegelFun_first_index_shift

set_option autoImplicit false

open Filter Topology

namespace N25

private theorem root_ne_one (s : ℤ) (hs : ¬(25 : ℤ) ∣ s) :
    Complex.exp (2 * Real.pi * Complex.I * (s : ℂ) / 25) ≠ 1 := by
  intro he
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp he
  rw [div_eq_iff (by norm_num : (25 : ℂ) ≠ 0)] at hn
  have hp : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  have h : (2 * Real.pi * Complex.I : ℂ) * (s : ℂ) =
      (2 * Real.pi * Complex.I) * ((n : ℂ) * 25) := by linear_combination hn
  have h' : s = n * 25 := by exact_mod_cast mul_left_cancel₀ hp h
  exact hs ⟨n, by rw [h']; ring⟩

/-- A nontrivial index has a nonzero leading analytic coefficient. -/
theorem _root_.solution (r s : ℤ)
    (hs : (25 : ℤ) ∣ r → ¬(25 : ℤ) ∣ s) :
    ∃ c : ℂ, c ≠ 0 ∧ Tendsto
      (fun τ : UpperHalfPlane => ModularCurve.siegelFun 25 r s (τ : ℂ) /
        Complex.exp (Real.pi * Complex.I *
          ((((r % 25 : ℤ) : ℂ) / 25) ^ 2 - ((r % 25 : ℤ) : ℂ) / 25 + 1 / 6) * (τ : ℂ)))
      UpperHalfPlane.atImInfty (nhds c) := by
  have hs0 : r % 25 = 0 → ¬(25 : ℤ) ∣ s := by
    intro h
    apply hs
    exact ⟨r / 25, by omega⟩
  obtain ⟨a, _, ha, _, _, hlim⟩ :=
    ModularCurve.SiegelUnit.exists_isIntegral_hasSum_siegelFun 25 (r % 25) s
      (by omega) (by norm_num; omega) hs0
  have ha0 : a 0 ≠ 0 := by
    rw [ha]
    split_ifs
    · exact sub_ne_zero.mpr (Ne.symm (root_ne_one s (hs0 ‹r % 25 = 0›)))
    · exact one_ne_zero
  let u : ℂ := -Complex.exp (-(Real.pi * Complex.I * (s : ℂ) / 25))
  let b : ℂ := -Complex.exp (Real.pi * Complex.I * (s : ℂ) *
    (((r % 25 : ℤ) : ℂ) - 25) / 25 ^ 2)
  have hu : u ≠ 0 := neg_ne_zero.mpr (Complex.exp_ne_zero _)
  have hb : b ≠ 0 := neg_ne_zero.mpr (Complex.exp_ne_zero _)
  refine ⟨(u ^ (r / 25) * b) * a 0, mul_ne_zero (mul_ne_zero (zpow_ne_zero _ hu) hb) ha0, ?_⟩
  have he (τ : UpperHalfPlane) :
      2 * Real.pi * Complex.I *
        (6 * (((r % 25 : ℤ) : ℂ)) ^ 2 - 6 * ((r % 25 : ℤ) : ℂ) * 25 + 25 ^ 2) * (τ : ℂ) /
          (12 * 25 ^ 2) =
      Real.pi * Complex.I *
        ((((r % 25 : ℤ) : ℂ) / 25) ^ 2 - ((r % 25 : ℤ) : ℂ) / 25 + 1 / 6) * (τ : ℂ) := by ring
  simp only [Nat.cast_ofNat] at hlim
  simp_rw [he] at hlim
  have hm := hlim.const_mul (u ^ (r / 25) * b)
  apply hm.congr'
  filter_upwards [] with τ
  have hshift := siegelFun_first_index_shift 25 (r % 25) s (r / 25) τ
  simp only [Nat.cast_ofNat] at hshift
  rw [show r % 25 + (r / 25) * (25 : ℤ) = r by omega] at hshift
  rw [hshift]
  change (u ^ (r / 25) * b) * (_ / (b * _)) = (u ^ (r / 25) * _) / _
  field_simp

end N25
