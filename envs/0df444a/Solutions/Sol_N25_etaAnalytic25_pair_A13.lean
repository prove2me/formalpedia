-- Prove2me | solution 1 for N25.etaAnalytic25_pair_A13
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:49:24.552124+00:00
-- url     : https://prove2.me/submissions/e544c0c0-d856-4dc7-bc8c-46f97fb427be

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_siegelDilation_gamma0
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_N25_siegelFun_first_index_shift
import Theorems.Thm_N25_siegelFun_reflect_first_index

set_option autoImplicit false

namespace N25

private theorem thirteen_index_pair_product (j : Fin 5) (τ : UpperHalfPlane) :
    let σ : Fin 5 → ℂ := ![-1,1,-1,-1,1]
    (-ModularCurve.siegelFun 25 (13*((unitResidues25 j).1 : ℤ)) 0 (25*(τ : ℂ))) *
      (-ModularCurve.siegelFun 25 (13*((unitResidues25 j).2 : ℤ)) 0 (25*(τ : ℂ))) =
    σ j * (etaAnalytic25 (unitResidues25 (j-1)).1 τ *
      etaAnalytic25 (unitResidues25 (j-1)).2 τ) := by
  let σ : Fin 5 → ℂ := ![-1,1,-1,-1,1]
  let E (r : ℤ) : ℂ := -ModularCurve.siegelFun 25 r 0 (25*(τ : ℂ))
  let τ25 : UpperHalfPlane := ⟨25*(τ : ℂ), by
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 25) τ.im_pos)⟩
  have shift (r k : ℤ) : E (r+k*25) = (-1 : ℂ)^k * E r := by
    simpa [E] using congrArg Neg.neg (siegelFun_first_index_shift 25 r 0 k τ25)
  have ref (r : ℤ) : E (25-r) = E r := by
    simpa only [Nat.cast_ofNat] using
      congrArg Neg.neg (siegelFun_reflect_first_index 25 r τ25)
  have h13 : E 13 = E 12 := by simpa using ref 12
  have h16 : E 16 = E 9 := by simpa using ref 9
  have h17 : E 17 = E 8 := by simpa using ref 8
  have h18 : E 18 = E 7 := by simpa using ref 7
  have h14 : E 14 = E 11 := by simpa using ref 11
  have h26 : E 26 = -E 1 := by
    have h := shift 1 1
    norm_num at h
    exact h
  have h39 : E 39 = -E 11 := by
    have h := shift 14 1
    norm_num at h
    rw [h14] at h
    exact h
  have h52 : E 52 = E 2 := by
    have h := shift 2 2
    norm_num at h
    exact h
  have h78 : E 78 = -E 3 := by
    have h := shift 3 3
    norm_num at h
    exact h
  have h91 : E 91 = -E 9 := by
    have h := shift 16 3
    norm_num at h
    rw [h16] at h
    exact h
  have h104 : E 104 = E 4 := by
    have h := shift 4 4
    norm_num at h
    exact h
  have h117 : E 117 = E 8 := by
    have h := shift 17 4
    norm_num at h
    exact h.trans h17
  have h143 : E 143 = -E 7 := by
    have h := shift 18 5
    norm_num at h
    rw [h18] at h
    exact h
  have h156 : E 156 = E 6 := by
    have h := shift 6 6
    norm_num at h
    exact h
  have hp (k : Fin 5) : k-1 =
      ⟨(k.val+4)%5, Nat.mod_lt _ (by decide)⟩ := by
    fin_cases k <;> decide
  change E (13*((unitResidues25 j).1 : ℤ)) * E (13*((unitResidues25 j).2 : ℤ)) =
    σ j * (E ((unitResidues25 (j-1)).1 : ℤ) * E ((unitResidues25 (j-1)).2 : ℤ))
  rw [hp]
  fin_cases j
  · norm_num [unitResidues25, σ]
    rw [h13, h91]
    ring
  · norm_num [unitResidues25, σ]
    rw [h26, h143]
    ring
  · norm_num [unitResidues25, σ]
    rw [h39, h52]
    ring
  · norm_num [unitResidues25, σ]
    rw [h78, h104]
    ring
  · norm_num [unitResidues25, σ]
    rw [h117, h156]
    ring

private theorem pair_phase_thirteen (g h : ℕ) (k : ℤ)
    (hsq : (g : ℤ)^2+(h : ℤ)^2 = 25*k)
    (hpar : Even (k-(g : ℤ)-(h : ℤ))) :
    Complex.exp (Real.pi * Complex.I * (13*(g : ℂ)^2/25-(g : ℂ))) *
      Complex.exp (Real.pi * Complex.I * (13*(h : ℂ)^2/25-(h : ℂ))) = 1 := by
  obtain ⟨n, hn⟩ := hpar
  have hsquare : (g : ℂ)^2+(h : ℂ)^2 = 25*(k : ℂ) := by exact_mod_cast hsq
  have hsum : (k : ℂ)-(g : ℂ)-(h : ℂ) = 2*(n : ℂ) := by
    exact_mod_cast (show k-(g : ℤ)-(h : ℤ) = 2*n by omega)
  rw [← Complex.exp_add]
  have he : Real.pi * Complex.I * (13*(g : ℂ)^2/25-(g : ℂ)) +
      Real.pi * Complex.I * (13*(h : ℂ)^2/25-(h : ℂ)) =
      ((6*k+n : ℤ) : ℂ) * (2*Real.pi*Complex.I) := by
    push_cast
    linear_combination (13*Real.pi*Complex.I/25)*hsquare + (Real.pi*Complex.I)*hsum
  rw [he]
  exact Complex.exp_int_mul_two_pi_mul_I _

/-- The forward label-thirteen matrix shifts the five original Siegel pairs
backward by one, with their exact common multiplier and individual signs. -/
theorem _root_.solution :
    let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
      ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
    let σ : Fin 5 → ℂ := ![-1,1,-1,-1,1]
    ∃ μ : ℂ, μ^12 = 1 ∧ ∀ (j : Fin 5) (τ : UpperHalfPlane),
      etaAnalytic25 (unitResidues25 j).1 (A • τ) *
        etaAnalytic25 (unitResidues25 j).2 (A • τ) =
      (μ^2 * σ j) * (etaAnalytic25 (unitResidues25 (j-1)).1 τ *
        etaAnalytic25 (unitResidues25 (j-1)).2 τ) := by
  let A : Matrix.SpecialLinearGroup (Fin 2) ℤ :=
    ⟨!![13,1;25,2], by norm_num [Matrix.det_fin_two]⟩
  let σ : Fin 5 → ℂ := ![-1,1,-1,-1,1]
  have hA : (25 : ℤ) ∣ (A : Matrix (Fin 2) (Fin 2) ℤ) 1 0 := by norm_num [A]
  obtain ⟨μ, hμ, htrans⟩ := siegelDilation_gamma0 A hA
  refine ⟨μ, hμ, ?_⟩
  intro j τ
  let C (g : ℕ) : ℂ := Real.pi * Complex.I * (13*(g : ℂ)^2/25-(g : ℂ))
  let E (r : ℤ) : ℂ := -ModularCurve.siegelFun 25 r 0 (25*(τ : ℂ))
  have ht (g : ℕ) : etaAnalytic25 g (A • τ) = μ * Complex.exp (C g) * E (13*(g : ℤ)) := by
    simpa [A, C, E, etaAnalytic25] using htrans (g : ℤ) τ
  have hphase : Complex.exp (C (unitResidues25 j).1) *
      Complex.exp (C (unitResidues25 j).2) = 1 := by
    apply pair_phase_thirteen (unitResidues25 j).1 (unitResidues25 j).2
      ((((unitResidues25 j).1 : ℤ)^2+((unitResidues25 j).2 : ℤ)^2)/25)
    · fin_cases j <;> norm_num [unitResidues25]
    · fin_cases j <;> norm_num [unitResidues25]
  rw [ht, ht]
  calc
    (μ * Complex.exp (C (unitResidues25 j).1) * E (13*((unitResidues25 j).1 : ℤ))) *
        (μ * Complex.exp (C (unitResidues25 j).2) * E (13*((unitResidues25 j).2 : ℤ))) =
      μ^2 * (Complex.exp (C (unitResidues25 j).1) * Complex.exp (C (unitResidues25 j).2)) *
        (E (13*((unitResidues25 j).1 : ℤ)) * E (13*((unitResidues25 j).2 : ℤ))) := by ring
    _ = (μ^2 * σ j) * (etaAnalytic25 (unitResidues25 (j-1)).1 τ *
        etaAnalytic25 (unitResidues25 (j-1)).2 τ) := by
      rw [hphase, mul_one, thirteen_index_pair_product]
      ring

end N25
