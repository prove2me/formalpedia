-- Prove2me | solution 1 for N25.etaAnalytic25_pair_A7
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:25.580631+00:00
-- url     : https://prove2.me/submissions/d828737d-2ef7-4e51-80d2-c597dd2fb891

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_siegelDilation_gamma0
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_N25_siegelFun_first_index_period_two_levels
import Theorems.Thm_N25_siegelFun_neg_first_index
import Theorems.Thm_N25_siegelFun_reflect_first_index
import Theorems.Thm_ModularCurve_SiegelUnit_siegelFun_add_level
import Theorems.Thm_KeystoneLadder_SameP1Vec_trans

set_option autoImplicit false

namespace N25

private theorem seven_index_pair_product (j : Fin 5) (τ : UpperHalfPlane) :
    (-ModularCurve.siegelFun 25 (7*((unitResidues25 j).1 : ℤ)) 0 (25*(τ : ℂ))) *
      (-ModularCurve.siegelFun 25 (7*((unitResidues25 j).2 : ℤ)) 0 (25*(τ : ℂ))) =
    -(etaAnalytic25 (unitResidues25 j).1 τ * etaAnalytic25 (unitResidues25 j).2 τ) := by
  let E (r : ℤ) : ℂ := -ModularCurve.siegelFun 25 r 0 (25*(τ : ℂ))
  let τ25 : UpperHalfPlane := ⟨25*(τ : ℂ), by
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 25) τ.im_pos)⟩
  have per (r k : ℤ) : E (r+50*k) = E r := by
    have h := congrArg Neg.neg (siegelFun_first_index_period_two_levels 25 r k τ25)
    norm_num only [Nat.cast_ofNat] at h
    rw [show r+50*k = r+2*k*(25 : ℤ) by ring]
    exact h
  have odd (r : ℤ) : E (-r) = -E r := by
    dsimp only [E]
    rw [siegelFun_neg_first_index]
  have ref (r : ℤ) : E (25-r) = E r := by
    simpa only [Nat.cast_ofNat] using
      congrArg Neg.neg (siegelFun_reflect_first_index 25 r τ25)
  have step (r : ℤ) : E (r+25) = -E r := by
    simpa [E] using congrArg Neg.neg
      ((ModularCurve.SiegelUnit.siegelFun_add_level 25 r 0).2 τ25)
  have h14 : E 14 = E 11 := by simpa using ref 11
  have h21 : E 21 = E 4 := by simpa using ref 4
  have h28 : E 28 = -E 3 := by simpa using step 3
  have h42 : E 42 = -E 8 := by simpa using (per (-8) 1).trans (odd 8)
  have h49 : E 49 = -E 1 := by simpa using (per (-1) 1).trans (odd 1)
  have h56 : E 56 = E 6 := by simpa using per 6 1
  have h63 : E 63 = E 12 := by simpa using (per 13 1).trans (ref 12)
  have h77 : E 77 = -E 2 := by simpa using (per 27 1).trans (step 2)
  have h84 : E 84 = -E 9 := by simpa using (per 34 1).trans (step 9)
  change E (7*((unitResidues25 j).1 : ℤ)) * E (7*((unitResidues25 j).2 : ℤ)) =
    -(E ((unitResidues25 j).1 : ℤ) * E ((unitResidues25 j).2 : ℤ))
  fin_cases j
  · norm_num [unitResidues25]
    rw [h49]
    ring
  · norm_num [unitResidues25]
    rw [h14, h77]
    ring
  · norm_num [unitResidues25]
    rw [h21, h28]
    ring
  · norm_num [unitResidues25]
    rw [h42, h56]
    ring
  · norm_num [unitResidues25]
    rw [h63, h84]
    ring

private theorem pair_phase_seven (g h : ℕ) (k : ℤ)
    (hsq : (g : ℤ)^2+(h : ℤ)^2 = 25*k)
    (hpar : Even (k-(g : ℤ)-(h : ℤ))) :
    Complex.exp (Real.pi * Complex.I *
      (7*5*(g : ℂ)^2/25-5*(g : ℂ))) *
    Complex.exp (Real.pi * Complex.I *
      (7*5*(h : ℂ)^2/25-5*(h : ℂ))) = 1 := by
  obtain ⟨n, hn⟩ := hpar
  have hsquare : (g : ℂ)^2+(h : ℂ)^2 = 25*(k : ℂ) := by exact_mod_cast hsq
  have hsum : (k : ℂ)-(g : ℂ)-(h : ℂ) = 2*(n : ℂ) := by
    exact_mod_cast (show k-(g : ℤ)-(h : ℤ) = 2*n by omega)
  rw [← Complex.exp_add]
  have he : Real.pi * Complex.I * (7*5*(g : ℂ)^2/25-5*(g : ℂ)) +
      Real.pi * Complex.I * (7*5*(h : ℂ)^2/25-5*(h : ℂ)) =
      ((15*k+5*n : ℤ) : ℂ) * (2*Real.pi*Complex.I) := by
    push_cast
    linear_combination (35*Real.pi*Complex.I/25)*hsquare + (5*Real.pi*Complex.I)*hsum
  rw [he]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- The literal matrix with entries seven, five, twenty-five and eighteen
has the same signed square multiplier on all five original Siegel pairs. -/
theorem _root_.solution :
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![7,5;25,18], by norm_num [Matrix.det_fin_two]⟩
    ∃ μ : ℂ, μ^12 = 1 ∧ ∀ (j : Fin 5) (τ : UpperHalfPlane),
      etaAnalytic25 (unitResidues25 j).1 (A • τ) *
        etaAnalytic25 (unitResidues25 j).2 (A • τ) =
      (-μ^2) * (etaAnalytic25 (unitResidues25 j).1 τ *
        etaAnalytic25 (unitResidues25 j).2 τ) := by
  let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![7,5;25,18], by norm_num [Matrix.det_fin_two]⟩
  have hA : (25 : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by norm_num [A]
  obtain ⟨μ, hμ, htrans⟩ := siegelDilation_gamma0 A hA
  refine ⟨μ, hμ, ?_⟩
  intro j τ
  let C (t : ℕ) : ℂ := Real.pi * Complex.I * (7*5*(t : ℂ)^2/25-5*(t : ℂ))
  let E (r : ℤ) : ℂ := -ModularCurve.siegelFun 25 r 0 (25*(τ : ℂ))
  have ht (g : ℕ) : etaAnalytic25 g (A • τ) = μ * Complex.exp (C g) * E (7*(g : ℤ)) := by
    simpa [A, C, E, etaAnalytic25] using htrans (g : ℤ) τ
  have hphase : Complex.exp (C (unitResidues25 j).1) *
      Complex.exp (C (unitResidues25 j).2) = 1 := by
    apply pair_phase_seven (unitResidues25 j).1 (unitResidues25 j).2
      ((((unitResidues25 j).1 : ℤ)^2+((unitResidues25 j).2 : ℤ)^2)/25)
    · fin_cases j <;> norm_num [unitResidues25]
    · fin_cases j <;> norm_num [unitResidues25]
  rw [ht, ht]
  calc
    (μ * Complex.exp (C (unitResidues25 j).1) * E (7*((unitResidues25 j).1 : ℤ))) *
        (μ * Complex.exp (C (unitResidues25 j).2) * E (7*((unitResidues25 j).2 : ℤ))) =
      μ^2 * (Complex.exp (C (unitResidues25 j).1) * Complex.exp (C (unitResidues25 j).2)) *
        (E (7*((unitResidues25 j).1 : ℤ)) * E (7*((unitResidues25 j).2 : ℤ))) := by ring
    _ = (-μ^2) * (etaAnalytic25 (unitResidues25 j).1 τ *
        etaAnalytic25 (unitResidues25 j).2 τ) := by
      rw [hphase, mul_one, seven_index_pair_product]
      ring

end N25
