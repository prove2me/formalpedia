-- Prove2me | solution 1 for OAI.DoublingHilbert.sum_scale_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T22:54:28.727719+00:00
-- url     : https://prove2.me/submissions/b1296757-d629-4226-b58b-96dad27e57bf

-- Generated from openai/math@1581d4c lean/OAI/Geometry/DoublingHilbert/Construction.lean:L381-L417
-- (upload_full_project.md Phase 4): solution for node OAI.DoublingHilbert.sum_scale_sq_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` restates it and is proved by it.
import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction

-- ---- from OAI.Geometry.DoublingHilbert.Construction ----
namespace OAI

/-! Recurrent scales and orthogonal displacement sheets in real Hilbert space. -/

open scoped BigOperators
open Set

noncomputable section

namespace DoublingHilbert

theorem scale_add (i j : ℕ) : scale (i + j) = scale i * (1000 : ℝ)⁻¹ ^ j := by
  simp only [scale]
  rw [show i + j + 1 = (i + 1) + j by omega, pow_add]

/-- A deliberately coarse geometric-tail bound, adequate for the covering constant. -/
theorem sum_scale_sq_le {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j ∈ s, scale j ≤ R) : ∑ j ∈ s, (scale j) ^ 2 ≤ 2 * R ^ 2 := by
  classical
  by_cases hse : s.Nonempty
  · let m := s.min' hse
    have hm : m ∈ s := s.min'_mem hse
    have hmj (j : ℕ) (hj : j ∈ s) : m ≤ j := s.min'_le j hj
    have hgeom := (summable_geometric_of_abs_lt_one (r := (1000000 : ℝ)⁻¹) (by norm_num)).sum_le_tsum
      (s.image (fun j => j - m)) (fun _ _ => by positivity)
    rw [tsum_geometric_of_abs_lt_one (by norm_num : |(1000000 : ℝ)⁻¹| < 1)] at hgeom
    have himage : (∑ j ∈ s.image (fun j => j - m), (1000000 : ℝ)⁻¹ ^ j) =
        ∑ j ∈ s, (1000000 : ℝ)⁻¹ ^ (j - m) := by
      apply Finset.sum_image
      intro i hi j hj he
      dsimp at he
      have := hmj i hi
      have := hmj j hj
      omega
    rw [himage] at hgeom
    have heq : (∑ j ∈ s, scale j ^ 2) = scale m ^ 2 *
        ∑ j ∈ s, (1000000 : ℝ)⁻¹ ^ (j - m) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : m + (j - m) = j := Nat.add_sub_of_le (hmj j hj)
      conv_lhs => rw [← hj', scale_add]
      rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    rw [heq]
    calc
      _ ≤ scale m ^ 2 * (1 - (1000000 : ℝ)⁻¹)⁻¹ :=
        mul_le_mul_of_nonneg_left hgeom (sq_nonneg _)
      _ ≤ 2 * scale m ^ 2 := by nlinarith [sq_nonneg (scale m)]
      _ ≤ 2 * R ^ 2 := by nlinarith [hs m hm, scale_pos m]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hse, Finset.sum_empty]
    positivity

end DoublingHilbert

end

end OAI

-- ---- platform node ----
open OAI OAI.DoublingHilbert
open scoped BigOperators
open Set

theorem solution {s : Finset ℕ} {R : ℝ} (hR : 0 ≤ R)
    (hs : ∀ j ∈ s, scale j ≤ R) : ∑ j ∈ s, (scale j) ^ 2 ≤ 2 * R ^ 2 := by
  first
    | exact OAI.DoublingHilbert.sum_scale_sq_le hR hs
    | exact OAI.DoublingHilbert.sum_scale_sq_le
    | (apply OAI.DoublingHilbert.sum_scale_sq_le <;> assumption)
    | (intros; apply OAI.DoublingHilbert.sum_scale_sq_le <;> assumption)
