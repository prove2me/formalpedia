-- Prove2me | solution 1 for NewMinimalStandardModel.quadratic_chaotic_inflation_predictions
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:59:32.567215+00:00
-- url     : https://prove2.me/submissions/e5d7763a-2f7f-42d0-8724-78b7bfd3844d

import Mathlib
import Definitions.Def_NewMinimalStandardModel_Defs

set_option autoImplicit false

open NewMinimalStandardModel in
theorem qci_deriv (m : ℝ) : deriv (quadraticPotential m) = fun x => m ^ 2 * x := by
  funext x
  have h : HasDerivAt (quadraticPotential m) (m ^ 2 * x) x := by
    have := ((hasDerivAt_pow 2 x).const_mul (m ^ 2)).div_const 2
    exact this.congr_deriv (by norm_num <;> ring)
  exact h.deriv

open NewMinimalStandardModel in
theorem qci_deriv2 (m : ℝ) : deriv (deriv (quadraticPotential m)) = fun _ => m ^ 2 := by
  rw [qci_deriv]
  funext x
  simp

open NewMinimalStandardModel in
theorem qci_ratio (m : ℝ) (hm : m ≠ 0) (ψ : ℝ) :
    quadraticPotential m ψ / deriv (quadraticPotential m) ψ = ψ / 2 := by
  rw [qci_deriv]
  unfold quadraticPotential
  rcases eq_or_ne ψ 0 with h | h
  · subst h; simp
  · field_simp

open NewMinimalStandardModel in
theorem qci_efolds (m Mpl a b : ℝ) (hm : m ≠ 0) :
    efolds (quadraticPotential m) Mpl a b = (1 / Mpl ^ 2) * ((b ^ 2 - a ^ 2) / 4) := by
  unfold efolds
  simp_rw [qci_ratio m hm]
  rw [intervalIntegral.integral_div, integral_id]
  ring

open NewMinimalStandardModel in
theorem qci_eps (m Mpl φ : ℝ) (hm : m ≠ 0) (hφ : φ ≠ 0) :
    slowRollEpsilon (quadraticPotential m) Mpl φ = 2 * Mpl ^ 2 / φ ^ 2 := by
  unfold slowRollEpsilon
  rw [qci_deriv]
  unfold quadraticPotential
  field_simp

open NewMinimalStandardModel in
theorem qci_eta (m Mpl φ : ℝ) (hm : m ≠ 0) (hφ : φ ≠ 0) :
    slowRollEta (quadraticPotential m) Mpl φ = 2 * Mpl ^ 2 / φ ^ 2 := by
  unfold slowRollEta
  rw [qci_deriv2]
  unfold quadraticPotential
  field_simp

open NewMinimalStandardModel in
theorem solution (m Mpl φstar N : ℝ) (hm : 0 < m)
    (hMpl : 0 < Mpl) (hφ : Real.sqrt 2 * Mpl < φstar)
    (hN : efolds (quadraticPotential m) Mpl (Real.sqrt 2 * Mpl) φstar = N) :
    slowRollEpsilon (quadraticPotential m) Mpl (Real.sqrt 2 * Mpl) = 1 ∧
    spectralIndex (quadraticPotential m) Mpl φstar = 1 - 4 / (2 * N + 1) ∧
    tensorToScalarRatio (quadraticPotential m) Mpl φstar = 16 / (2 * N + 1) ∧
    (N = 50 →
      |spectralIndex (quadraticPotential m) Mpl φstar - 0.96| < 0.005 ∧
      |tensorToScalarRatio (quadraticPotential m) Mpl φstar - 0.16| < 0.005) := by
  have hm0 : m ≠ 0 := hm.ne'
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 < Real.sqrt 2 := by positivity
  have ha0 : 0 < Real.sqrt 2 * Mpl := by positivity
  have hφ0 : 0 < φstar := ha0.trans hφ
  rw [qci_efolds m Mpl _ _ hm0] at hN
  have hNe : 2 * N + 1 = φstar ^ 2 / (2 * Mpl ^ 2) := by
    rw [← hN, mul_pow, hs2]; field_simp; ring
  have hNpos : 0 < 2 * N + 1 := by rw [hNe]; positivity
  have hns : spectralIndex (quadraticPotential m) Mpl φstar = 1 - 4 / (2 * N + 1) := by
    unfold spectralIndex
    rw [qci_eps m Mpl φstar hm0 hφ0.ne', qci_eta m Mpl φstar hm0 hφ0.ne', hNe]
    field_simp; ring
  have hr : tensorToScalarRatio (quadraticPotential m) Mpl φstar = 16 / (2 * N + 1) := by
    unfold tensorToScalarRatio
    rw [qci_eps m Mpl φstar hm0 hφ0.ne', hNe]
    field_simp
  refine ⟨?_, hns, hr, ?_⟩
  · rw [qci_eps m Mpl _ hm0 ha0.ne', mul_pow, hs2]
    field_simp
  · intro h50
    rw [hns, hr, h50]
    constructor <;> rw [abs_lt] <;> constructor <;> norm_num
