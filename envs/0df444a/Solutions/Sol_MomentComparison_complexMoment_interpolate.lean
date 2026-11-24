-- Prove2me | solution 1 for MomentComparison.complexMoment_interpolate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T11:09:00.410116+00:00
-- url     : https://prove2.me/submissions/70094e0d-9dad-4708-b019-34b09834c5e8

module
public import Definitions.Def_MomentComparison_Basic
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Definitions.Def_MomentComparison_Basic
import all Definitions.Def_MomentComparison_Basic
public import Definitions.Def_MomentComparison_MomentNorm

set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators
open MomentComparison
namespace MomentComparison
theorem _root_.solution {n : ℕ} (f : Cube n → ℂ) {a b u : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hu : 0 < u) (hu' : u < 1) :
    cubeAverage (fun x => ‖f x‖ ^ ((1 - u) * a + u * b)) ≤
      cubeAverage (fun x => ‖f x‖ ^ a) ^ (1 - u) *
      cubeAverage (fun x => ‖f x‖ ^ b) ^ u := by
  let A : Cube n → ℝ := fun x => ‖f x‖ ^ a / (2 : ℝ) ^ n
  let B : Cube n → ℝ := fun x => ‖f x‖ ^ b / (2 : ℝ) ^ n
  have hA (x) : 0 ≤ A x := by dsimp [A]; positivity
  have hB (x) : 0 ≤ B x := by dsimp [B]; positivity
  have hconj : ((1 - u)⁻¹).HolderConjugate u⁻¹ :=
    Real.holderConjugate_iff.mpr
      ⟨(one_lt_inv₀ (by linarith)).mpr (by linarith), by simp⟩
  have hH := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun x => A x ^ (1 - u)) (g := fun x => B x ^ u) hconj
    (fun x _ => Real.rpow_nonneg (hA x) _) (fun x _ => Real.rpow_nonneg (hB x) _)
  have hA' (x) : (A x ^ (1 - u)) ^ (1 - u)⁻¹ = A x := by
    rw [← Real.rpow_mul (hA x), mul_inv_cancel₀ (by linarith : 1 - u ≠ 0), Real.rpow_one]
  have hB' (x) : (B x ^ u) ^ u⁻¹ = B x := by
    rw [← Real.rpow_mul (hB x), mul_inv_cancel₀ hu.ne', Real.rpow_one]
  simp only [hA', hB', one_div, inv_inv] at hH
  have hterm (x) :
      A x ^ (1 - u) * B x ^ u =
        ‖f x‖ ^ ((1 - u) * a + u * b) / (2 : ℝ) ^ n := by
    dsimp [A, B]
    have hN : 0 < (2 : ℝ) ^ n := by positivity
    rw [Real.div_rpow (Real.rpow_nonneg (norm_nonneg _) _) hN.le,
      Real.div_rpow (Real.rpow_nonneg (norm_nonneg _) _) hN.le,
      div_mul_div_comm, ← Real.rpow_add hN]
    rw [sub_add_cancel, Real.rpow_one,
      ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_add_of_nonneg (norm_nonneg _) (mul_nonneg ha (by linarith))
        (mul_nonneg hb hu.le)]
    congr 2
    ring
  simpa only [hterm, A, B, ← Finset.sum_div, cubeAverage] using hH
end MomentComparison
