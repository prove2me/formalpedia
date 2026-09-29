-- Prove2me | solution 1 for MTT.Cohomology.evaluation_faithful
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-06T16:51:35.613768+00:00
-- url     : https://prove2.me/submissions/e37d0f7f-a999-455a-b326-71e7d5304cac

import Definitions.Def_MTT_Cohomology

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open MTT.Cohomology

namespace P2MEF

open MvPolynomial

variable {N n : ℕ} {R : Type*} [CommRing R]

/-- The exponent vector of `X^j Y^(n-j)`, exactly as it occurs in `evaluation`. -/
def mono (n j : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i : Fin 2 => if i = 0 then j else n - j)

theorem mono_apply (n j : ℕ) (i : Fin 2) : mono n j i = if i = 0 then j else n - j := rfl

theorem evaluation_apply (j : ℕ) (r : ℚ) (φ : Hc N n R) :
    evaluation j r φ = MvPolynomial.coeff (mono n j) (φ.val (OnePoint.infty, (r : Cusp))) :=
  rfl

theorem deg_eq (d : Fin 2 →₀ ℕ) : d.degree = d 0 + d 1 := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]

/-- A degree-`n` exponent vector in two variables is `X^j Y^(n-j)` for `j = d 0`. -/
theorem eq_mono (d : Fin 2 →₀ ℕ) (j : ℕ) (hj : d 0 = j) (hd : d.degree = n) :
    d = mono n j := by
  rw [deg_eq] at hd
  ext i
  have hi : i = 0 ∨ i = 1 := by fin_cases i <;> simp
  rcases hi with rfl | rfl
  · rw [mono_apply]; simp [hj]
  · rw [mono_apply]; simp; omega

/-- A class all of whose integral evaluations on `[∞] − [r]` vanish is zero on those paths. -/
theorem val_infty_eq_zero (φ : Hc N n R)
    (h : ∀ j r, j ≤ n → evaluation j r φ = 0) (r : ℚ) :
    φ.val (OnePoint.infty, (r : Cusp)) = 0 := by
  have hhom : (φ.val (OnePoint.infty, (r : Cusp))).IsHomogeneous n :=
    (MvPolynomial.mem_homogeneousSubmodule _ _).mp (φ.2.1 _ _)
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [MvPolynomial.coeff_zero]
  by_cases hd : d.degree = n
  · have hle : d 0 ≤ n := by rw [deg_eq] at hd; omega
    rw [eq_mono d (d 0) rfl hd]
    exact h (d 0) r hle
  · exact hhom.coeff_eq_zero hd

theorem diag_zero (φ : Hc N n R) (x : Cusp) : φ.val (x, x) = 0 := by
  have h := φ.2.2.1 x x x
  have h2 : φ.val (x, x) + φ.val (x, x) - φ.val (x, x) = 0 := by rw [h]; simp
  simpa using h2

theorem val_eq (φ : Hc N n R) (x y : Cusp) :
    φ.val (x, y) = φ.val (OnePoint.infty, y) - φ.val (OnePoint.infty, x) := by
  have h := φ.2.2.1 OnePoint.infty x y
  rw [← h]; ring

/-- Integral coefficient evaluation on the paths `[∞] − [r]` is faithful. -/
theorem hc_eq_zero_of_evaluations (φ : Hc N n R)
    (h : ∀ j r, j ≤ n → evaluation j r φ = 0) : φ = 0 := by
  have hall : ∀ y : Cusp, φ.val (OnePoint.infty, y) = 0 := by
    intro y
    induction y using OnePoint.rec with
    | infty => exact diag_zero φ _
    | coe r => exact val_infty_eq_zero φ h r
  refine Subtype.ext (funext fun D => ?_)
  obtain ⟨x, y⟩ := D
  show φ.val (x, y) = 0
  rw [val_eq φ x y, hall, hall, sub_zero]

end P2MEF

open P2MEF in
theorem solution {N n : ℕ} {R : Type*} [CommRing R] (φ ψ : Hc N n R)
    (h : ∀ j r, j ≤ n → evaluation j r φ = evaluation j r ψ) : φ = ψ := by
  have := hc_eq_zero_of_evaluations (φ - ψ) (fun j r hj => by
    rw [map_sub, h j r hj, sub_self])
  exact sub_eq_zero.mp this
