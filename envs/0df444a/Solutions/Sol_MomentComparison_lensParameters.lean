-- Prove2me | solution 1 for MomentComparison.lensParameters
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:03:41.331317+00:00
-- url     : https://prove2.me/submissions/2be543e4-6881-4a44-82dd-e91aaa0afc4c

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
    let r := Real.sqrt (p - 1)
    let β := (2 * Real.pi - 2 * Real.arcsin (2 * r / p)) / Real.pi
    let k := (p - 2) / (2 * r)
    0 < r ∧ r ^ 2 = p - 1 ∧ 0 < β ∧ β < 2 ∧
      Real.cos (β * Real.pi / 2) + k * Real.sin (β * Real.pi / 2) = 0 := by
  let r := Real.sqrt (p - 1)
  let a := Real.arcsin (2 * r / p)
  let β := (2 * Real.pi - 2 * a) / Real.pi
  let k := (p - 2) / (2 * r)
  have hr : 0 < r := Real.sqrt_pos.2 (by linarith)
  have hr2 : r ^ 2 = p - 1 := Real.sq_sqrt (by linarith)
  have hp0 : 0 < p := by linarith
  have hy0 : 0 < 2 * r / p := by positivity
  have hy1 : 2 * r / p < 1 := by
    apply (div_lt_one hp0).mpr
    have hs : (2 * r) ^ 2 < p ^ 2 := by
      nlinarith only [hr2, sq_pos_of_pos (show 0 < p - 2 by linarith)]
    nlinarith only [hs, hr, hp0]
  have ha0 : 0 < a := Real.arcsin_pos.mpr hy0
  have ha1 : a < Real.pi / 2 := Real.arcsin_lt_pi_div_two.mpr hy1
  refine ⟨hr, hr2, div_pos (by linarith [Real.pi_pos]) Real.pi_pos,
    (div_lt_iff₀ Real.pi_pos).mpr (by linarith), ?_⟩
  change Real.cos (β * Real.pi / 2) + k * Real.sin (β * Real.pi / 2) = 0
  have hβ : β * Real.pi / 2 = Real.pi - a := by
    dsimp [β]
    field_simp [Real.pi_ne_zero]
  have hc : Real.cos a = (p - 2) / p := by
    dsimp [a]
    rw [Real.cos_arcsin]
    refine (Real.sqrt_eq_iff_eq_sq (by nlinarith [sq_nonneg (2 * r / p)])
      (by positivity)).mpr ?_
    field_simp
    nlinarith [hr2]
  rw [hβ, Real.sin_pi_sub, Real.cos_pi_sub, hc, Real.sin_arcsin (by linarith) hy1.le]
  dsimp [k]
  field_simp [hp0.ne', hr.ne']
  ring
end MomentComparison
