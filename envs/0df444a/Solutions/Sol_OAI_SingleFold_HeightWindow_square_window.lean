-- Prove2me | solution 1 for OAI.SingleFold.HeightWindow.square_window
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T18:25:44.589985+00:00
-- url     : https://prove2.me/submissions/0fb72382-d60d-406e-b17a-832bd1643ce1

import Mathlib
import Definitions.Def_SingleFold
import Definitions.Def_OAI_NumberTheory_SingleFold_PolynomialCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_RationalCodes
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticCoordinates
import Definitions.Def_OAI_NumberTheory_SingleFold_FunctionalCompiler
import Definitions.Def_OAI_NumberTheory_SingleFold_DescentMap
import Definitions.Def_OAI_NumberTheory_SingleFold_SquareSupport
import Definitions.Def_OAI_NumberTheory_SingleFold_LocalDescent
import Definitions.Def_OAI_NumberTheory_SingleFold_EllipticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_QuadraticHeight
import Definitions.Def_OAI_NumberTheory_SingleFold_FiniteGeneration
import Definitions.Def_OAI_NumberTheory_SingleFold_Rank
import Definitions.Def_OAI_NumberTheory_SingleFold_Duplication
import Definitions.Def_OAI_NumberTheory_SingleFold_Torsion

open OAI OAI.SingleFold
theorem h49_le_iff_log {P Q κ : ℕ} (hP : 0 < P) (hQ : 0 < Q) (hκ : 0 < κ) :
    P ≤ κ * Q ↔ Real.log P ≤ Real.log κ + Real.log Q := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  rw [Real.log_le_log_iff (by positivity) (by positivity)]
  constructor
  · intro h; exact_mod_cast h
  · intro h; exact_mod_cast h

theorem solution {W : ℕ → ℕ} {a c : ℝ} {κ k r : ℕ}
    (hW : ∀ j, 0 < W j)
    (happrox : ∀ j, 1 ≤ j → |Real.log (W j : ℝ) - a * (j : ℝ) ^ 2| ≤ c)
    (hc : 0 ≤ c) (hκ : 0 < κ) (h₁ : 6 * c < Real.log κ)
    (h₂ : Real.log κ < 2 * a - 6 * c) (hk : 1 ≤ k) (hr : 1 ≤ r) :
    (W (2 * k) * W r * W 1 ≤ κ * (W k ^ 2 * W (r + 1)) ∧
      W k ^ 2 * W (r + 1) ≤ κ * (W (2 * k) * W r * W 1)) ↔ r = k ^ 2 := by
  have hpos : ∀ j, (0:ℝ) < W j := fun j => by exact_mod_cast hW j
  have hk2 : 1 ≤ 2 * k := by omega
  have e1 := happrox (2*k) hk2
  have e2 := happrox r hr
  have e3 := happrox 1 le_rfl
  have e4 := happrox k hk
  have e5 := happrox (r+1) (by omega)
  rw [abs_le] at e1 e2 e3 e4 e5
  push_cast at e1 e2 e3 e4 e5
  have hP : 0 < W (2 * k) * W r * W 1 := Nat.mul_pos (Nat.mul_pos (hW _) (hW _)) (hW _)
  have hQ : 0 < W k ^ 2 * W (r + 1) := Nat.mul_pos (pow_pos (hW _) 2) (hW _)
  rw [h49_le_iff_log hP hQ hκ, h49_le_iff_log hQ hP hκ]
  push_cast
  rw [Real.log_mul (mul_pos (hpos _) (hpos _)).ne' (hpos 1).ne', Real.log_mul (hpos _).ne' (hpos r).ne',
    Real.log_mul (pow_pos (hpos k) 2).ne' (hpos _).ne', Real.log_pow]
  push_cast
  set A := Real.log (W (2*k)) + Real.log (W r) + Real.log (W 1) - 2 * Real.log (W k) - Real.log (W (r+1))
    with hA
  have hAu : A ≤ 2 * a * ((k:ℝ)^2 - r) + 6 * c := by rw [hA]; nlinarith
  have hAl : 2 * a * ((k:ℝ)^2 - r) - 6 * c ≤ A := by rw [hA]; nlinarith
  have ha : 0 < a := by nlinarith
  constructor
  · rintro ⟨h1, h2⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have : (r:ℝ) + 1 ≤ (k:ℝ)^2 := by exact_mod_cast (show r + 1 ≤ k^2 by omega)
      have : 2 * a ≤ 2 * a * ((k:ℝ)^2 - r) := by nlinarith
      linarith
    · have : (k:ℝ)^2 + 1 ≤ r := by exact_mod_cast (show k^2 + 1 ≤ r by omega)
      have : 2 * a ≤ 2 * a * (r - (k:ℝ)^2) := by nlinarith
      linarith
  · intro hrk
    have : (r:ℝ) = (k:ℝ)^2 := by exact_mod_cast hrk
    rw [this, sub_self, mul_zero] at hAu hAl
    constructor <;> linarith

