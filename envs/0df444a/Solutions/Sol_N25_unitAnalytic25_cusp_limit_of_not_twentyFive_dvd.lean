-- Prove2me | solution 1 for N25.unitAnalytic25_cusp_limit_of_not_twentyFive_dvd
-- status  : ACCEPTED   (prove)
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:49.896759+00:00
-- url     : https://prove2.me/submissions/b402cdb9-1a16-48a8-a4d9-934b1b39fa52

import Mathlib
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_N25_unitAnalytic25_affine_leading_limit
import Definitions.Def_ModularCurve_SiegelFunction
import Theorems.Thm_N25_matrix_det25_triangular
import Theorems.Thm_N25_dilation25_triangular_action
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_N25_dilation25_triangular_five_dvd
import Theorems.Thm_N25_unitResidues25_bernoulli_zero_of_five_dvd

set_option autoImplicit false

open Filter Topology

namespace N25

/-- At every direction of width five or twenty-five the unit has a finite nonzero limit. -/
theorem _root_.solution
    (i : Fin 5) (A : Matrix.SpecialLinearGroup (Fin 2) ℤ)
    (hA : ¬ (25 : ℤ) ∣ A 1 0) :
    ∃ c : ℂ, c ≠ 0 ∧ Filter.Tendsto
      (fun τ : UpperHalfPlane => unitAnalytic25 i (A • τ))
      UpperHalfPlane.atImInfty (nhds c) := by
  let M : Matrix (Fin 2) (Fin 2) ℤ := !![25,0;0,1] * (A : Matrix (Fin 2) (Fin 2) ℤ)
  have hM : M.det = 25 := by
    dsimp only [M]
    rw [Matrix.det_mul, A.prop]
    norm_num [Matrix.det_fin_two]
  obtain ⟨B, d, e, v, _, hd, he, hde, hm⟩ := matrix_det25_triangular M hM
  let a : ℝ := (d : ℝ)/(e : ℝ)
  let b : ℝ := (v : ℝ)/(e : ℝ)
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have ha : 0 < a := div_pos hdR heR
  let φ (τ : UpperHalfPlane) : UpperHalfPlane :=
    ⟨(a : ℂ)*(τ : ℂ)+(b : ℂ), by simpa using mul_pos ha τ.im_pos⟩
  have hφ (τ : UpperHalfPlane) : (φ τ : ℂ) = (a : ℂ)*(τ : ℂ)+(b : ℂ) := rfl
  have harg (τ : UpperHalfPlane) : ((B • φ τ : UpperHalfPlane) : ℂ) =
      25*((A • τ : UpperHalfPlane) : ℂ) := by
    obtain ⟨z, hz, hact⟩ := dilation25_triangular_action A B (d : ℤ) e v
      (by exact_mod_cast hd) he hm τ
    have hf : φ τ = z := by
      apply UpperHalfPlane.ext
      rw [hz]
      dsimp only [φ, a, b]
      push_cast
      ring
    rw [hf]
    exact hact
  let β : ℕ → ℝ := fun g =>
    (((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25)^2 -
      ((((g : ℤ)*B 0 0)%25 : ℤ) : ℝ)/25 + 1/6
  let βQ : ℕ → ℚ := fun g =>
    ((((B 0 0*(g : ℤ))%25 : ℤ) : ℚ))^2/625 -
      (((B 0 0*(g : ℤ))%25 : ℤ) : ℚ)/25 + 1/6
  let diff : ℝ := β (unitResidues25 i).1+β (unitResidues25 i).2-
    (β (unitResidues25 (i+1)).1+β (unitResidues25 (i+1)).2)
  have hβ (g : ℕ) : β g = (βQ g : ℝ) := by
    dsimp only [β, βQ]
    rw [mul_comm (g : ℤ) (B 0 0)]
    push_cast
    ring
  have hB : (5 : ℤ) ∣ B 0 0 :=
    dilation25_triangular_five_dvd A B d e v hd he hde hm hA
  have hzero : diff = 0 := by
    dsimp only [diff]
    simp only [hβ]
    dsimp only [βQ]
    have hq := unitResidues25_bernoulli_zero_of_five_dvd (B 0 0) hB i
    dsimp only at hq
    exact_mod_cast hq
  obtain ⟨c, hc, hl⟩ := unitAnalytic25_affine_leading_limit i A B φ a b ha hφ harg
  refine ⟨c, hc, ?_⟩
  change Filter.Tendsto
    (fun τ : UpperHalfPlane => unitAnalytic25 i (A • τ) /
      Complex.exp (Real.pi * Complex.I * ((diff * a : ℝ) : ℂ) * (τ : ℂ)))
    UpperHalfPlane.atImInfty (nhds c) at hl
  simpa only [hzero, zero_mul, Complex.ofReal_zero, mul_zero, Complex.exp_zero, div_one] using hl

end N25
