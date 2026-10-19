-- Prove2me | solution 1 for OAI.DirectCrouzeix.positive_block_hsSq
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:42:48.354401+00:00
-- url     : https://prove2.me/submissions/f77e907f-e6fd-4efc-85e0-218092048fb3

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/PositiveBlocks.lean:L35-L62
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.positive_block_hsSq. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks

-- ---- from OAI.Analysis.DirectCrouzeix.PositiveBlocks ----
namespace OAI

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem re_trace_mul_nonneg {ι : Type u_5} [Fintype ι] [DecidableEq ι]
    {A B : Matrix ι ι ℂ} (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  obtain ⟨C, hC⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hA.nonneg
  rw [hC, Matrix.star_eq_conjTranspose, Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
  exact (Complex.nonneg_iff.mp (hB.mul_mul_conjTranspose_same C).trace_nonneg).1

theorem re_trace_block_comparison {ι : Type u_6} [Fintype ι] [DecidableEq ι]
    (D J : Matrix ι ι ℂ) (hD : D.PosSemidef) (hJ : J.IsHermitian) :
    0 ≤ (Matrix.trace (D * J * D * J)).re := by
  have hp := re_trace_mul_nonneg hD (hD.mul_mul_conjTranspose_same J)
  simpa only [hJ.eq, Matrix.mul_assoc] using hp

theorem positive_block_hsSq {ι : Type u_7} [Fintype ι] [DecidableEq ι]
    {U V Z : Matrix ι ι ℂ}
    (h : (Matrix.fromBlocks U Zᴴ Z V).PosSemidef) :
    2 * hsSq Z ≤ hsSq U + hsSq V := by
  let D := Matrix.fromBlocks U Zᴴ Z V
  let J : Matrix (Sum ι ι) (Sum ι ι) ℂ := Matrix.fromBlocks 1 0 0 (-1)
  have hJ : J.IsHermitian := by
    exact Matrix.IsHermitian.fromBlocks Matrix.isHermitian_one (by simp)
      Matrix.isHermitian_one.neg
  have hU : U.IsHermitian := by
    have hh := h.isHermitian
    exact hh.submatrix Sum.inl
  have hV : V.IsHermitian := by
    have hh := h.isHermitian
    exact hh.submatrix Sum.inr
  have hp := re_trace_block_comparison D J h hJ
  have trace_blocks (A B C E : Matrix ι ι ℂ) :
      Matrix.trace (Matrix.fromBlocks A B C E) = Matrix.trace A + Matrix.trace E := by
    simp [Matrix.trace]
  have he : Matrix.trace (D * J * D * J) =
      Matrix.trace (U * U) + Matrix.trace (V * V) -
        2 * Matrix.trace (Zᴴ * Z) := by
    simp [D, J, Matrix.fromBlocks_multiply, trace_blocks,
      Matrix.trace_mul_comm Z Zᴴ]
    ring
  rw [he] at hp
  norm_num at hp
  simpa only [hsSq, hU.eq, hV.eq] using hp

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.positive_block_hsSq := @_root_.OAI.DirectCrouzeix.positive_block_hsSq
