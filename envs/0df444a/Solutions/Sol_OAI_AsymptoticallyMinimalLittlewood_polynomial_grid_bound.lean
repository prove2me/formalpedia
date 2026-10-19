-- Prove2me | solution 1 for OAI.AsymptoticallyMinimalLittlewood.polynomial_grid_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:59:53.394718+00:00
-- url     : https://prove2.me/submissions/38a221a3-829a-4def-ada1-ab40e29b8d37

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Littlewood/Rounding.lean:L1173-L1228
-- (upload_full_project.md Phase 4): solution for node OAI.AsymptoticallyMinimalLittlewood.polynomial_grid_bound. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_grid_dirichlet_square
import Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_grid_reproduce_monomial

-- ---- from OAI.Analysis.Littlewood.Rounding ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

universe u v w

namespace AsymptoticallyMinimalLittlewood
noncomputable section
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff

open scoped ComplexConjugate
open Finset

/-- No logarithmic loss: an oversampled analytic polynomial is controlled on the whole circle. -/
theorem polynomial_grid_bound {N M : ℕ} [NeZero M] (hN : 0 < N) (hNM : 2 * N ≤ M)
    (c : Fin N → ℂ) {G : ℝ} (hG : 0 ≤ G)
    (hgrid : ∀ j : ZMod M, ‖∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)‖ ≤ G)
    {z : ℂ} (hz : ‖z‖ = 1) :
    ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ ≤ 2 * G := by
  have hid : (M : ℂ) * N * (∑ k : Fin N, c k * z ^ (k : ℕ)) =
      ∑ j : ZMod M, (∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
        gridDirichlet (2 * N) z j * conj (gridDirichlet N z j) := by
    rw [Finset.mul_sum]
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro k hk
    calc
      _ = c k * ((M : ℂ) * N * z ^ (k : ℕ)) := by ring
      _ = c k * (∑ j : ZMod M, ZMod.stdAddChar j ^ (k : ℕ) *
          gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)) := by
        rw [grid_reproduce_monomial hNM k hz]
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
  have h2N := grid_dirichlet_square (n := 2 * N) hNM hz
  have hN' := grid_dirichlet_square (n := N) (by omega : N ≤ M) hz
  change (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ ^ 2) = _ at h2N
  change (∑ j : ZMod M, ‖gridDirichlet N z j‖ ^ 2) = _ at hN'
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (ZMod M))
    (fun j ↦ ‖gridDirichlet (2 * N) z j‖) (fun j ↦ ‖gridDirichlet N z j‖)
  rw [h2N, hN'] at hcs
  have hMpos : (0 : ℝ) < M := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne M)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hkernel : (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ *
      ‖gridDirichlet N z j‖) ≤ 2 * M * N := by
    push_cast at hcs
    nlinarith [mul_pos hMpos hNpos]
  have hnorm : (M : ℝ) * N * ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ =
      ‖∑ j : ZMod M, (∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
        gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)‖ := by
    rw [← hid, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_natCast]
  have hbound : (M : ℝ) * N * ‖∑ k : Fin N, c k * z ^ (k : ℕ)‖ ≤
      G * (2 * M * N) := by
    rw [hnorm]
    calc
      _ ≤ ∑ j : ZMod M, ‖(∑ k : Fin N, c k * ZMod.stdAddChar j ^ (k : ℕ)) *
          gridDirichlet (2 * N) z j * conj (gridDirichlet N z j)‖ := norm_sum_le _ _
      _ ≤ ∑ j : ZMod M, G * (‖gridDirichlet (2 * N) z j‖ *
          ‖gridDirichlet N z j‖) := Finset.sum_le_sum fun j _ ↦ by
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        nlinarith [mul_le_mul_of_nonneg_right (hgrid j)
          (mul_nonneg (norm_nonneg (gridDirichlet (2 * N) z j)) (norm_nonneg (gridDirichlet N z j)))]
      _ = G * (∑ j : ZMod M, ‖gridDirichlet (2 * N) z j‖ *
          ‖gridDirichlet N z j‖) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hkernel hG
  nlinarith [mul_pos hMpos hNpos]

end

end AsymptoticallyMinimalLittlewood

end OAI

-- ---- platform node ----
open OAI OAI.AsymptoticallyMinimalLittlewood
open MeasureTheory Complex Real FourierTransform Filter Topology
open scoped FourierTransform SchwartzMap ContDiff
open scoped ComplexConjugate
open Finset


theorem solution : type_of% @_root_.OAI.AsymptoticallyMinimalLittlewood.polynomial_grid_bound := @_root_.OAI.AsymptoticallyMinimalLittlewood.polynomial_grid_bound
