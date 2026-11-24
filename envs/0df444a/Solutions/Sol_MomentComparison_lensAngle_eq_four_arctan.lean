-- Prove2me | solution 1 for MomentComparison.lensAngle_eq_four_arctan
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:03:39.472218+00:00
-- url     : https://prove2.me/submissions/45bf159c-f0b9-4ac1-b6ff-8643a00c9695

module
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_LensAngle

set_option autoImplicit true
@[expose] public section
public section
open MomentComparison
namespace MomentComparison
theorem _root_.solution {p : ℝ} (hp : 2 < p) :
    2 * Real.arcsin (2 * Real.sqrt (p - 1) / p) =
      4 * Real.arctan (Real.sqrt (p - 1))⁻¹ := by
  let r := Real.sqrt (p - 1)
  have hsq : r ^ 2 = p - 1 := Real.sq_sqrt (by linarith)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr1 : 1 < r := (Real.lt_sqrt (by norm_num)).2 (by linarith)
  have hsin : Real.sin (2 * Real.arctan r⁻¹) = 2 * r / p := by
    rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
    have hss := Real.sq_sqrt (x := 1 + r⁻¹ ^ 2) (by positivity)
    have hs : 0 < Real.sqrt (1 + r⁻¹ ^ 2) := Real.sqrt_pos.2 (by positivity)
    calc
      _ = (2 * r⁻¹) / (Real.sqrt (1 + r⁻¹ ^ 2) ^ 2) := by
        field_simp [hs.ne']
      _ = (2 * r⁻¹) / (1 + r⁻¹ ^ 2) := by rw [hss]
      _ = _ := by
        field_simp [hr.ne', show p ≠ 0 by linarith]
        nlinarith [congrArg (fun y : ℝ => r * y) hsq]
  have ha₀ : 0 ≤ Real.arctan r⁻¹ := Real.arctan_nonneg.2 (inv_nonneg.2 hr.le)
  have ha₁ : Real.arctan r⁻¹ < Real.pi / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono (inv_lt_one_of_one_lt₀ hr1)
  have he := Real.arcsin_eq_of_sin_eq hsin
    ⟨by linarith [Real.pi_pos], by linarith⟩
  change 2 * Real.arcsin (2 * r / p) = 4 * Real.arctan r⁻¹
  rw [he]
  ring
end MomentComparison
