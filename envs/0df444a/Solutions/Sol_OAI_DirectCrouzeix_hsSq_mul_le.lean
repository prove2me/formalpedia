-- Prove2me | solution 1 for OAI.DirectCrouzeix.hsSq_mul_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T06:46:51.219977+00:00
-- url     : https://prove2.me/submissions/f399c3c5-be42-4094-ac91-e3fd555f7c54

-- Generated from openai/math@1581d4c lean/OAI/Analysis/DirectCrouzeix/HilbertSchmidt.lean:L62-L83
-- (upload_full_project.md Phase 4): solution for node OAI.DirectCrouzeix.hsSq_mul_le. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt

-- ---- from OAI.Analysis.DirectCrouzeix.HilbertSchmidt ----
namespace OAI

universe u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25
  u_26 u_27 u_28 u_29 u_30 u_31 u_32 u_33 u_34 u_35 u_36

noncomputable section

open scoped Matrix Matrix.Norms.L2Operator Kronecker

namespace DirectCrouzeix

open scoped MatrixOrder ComplexOrder

theorem hsSq_mul_le {ι : Type u_24} {κ : Type u_25} {τ : Type u_26} [Fintype ι] [Fintype κ]
    [Fintype τ]
    [DecidableEq κ] (F : Matrix ι κ ℂ) (G : Matrix κ τ ℂ) :
    hsSq (F * G) ≤ ‖F‖ ^ 2 * hsSq G := by
  have col (M : Matrix ι τ ℂ) :
      hsSq M = ∑ j, ‖(WithLp.toLp 2 (fun i => M i j) : EuclideanSpace ℂ ι)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, hsSq_eq_sum_norm_sq]
    exact Finset.sum_comm
  have colG : hsSq G = ∑ j,
      ‖(WithLp.toLp 2 (fun i => G i j) : EuclideanSpace ℂ κ)‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, hsSq_eq_sum_norm_sq]
    exact Finset.sum_comm
  rw [col, colG, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  have h := Matrix.l2_opNorm_mulVec F (WithLp.toLp 2 (fun i => G i j))
  have h' : ‖(WithLp.toLp 2 (fun i => (F * G) i j) : EuclideanSpace ℂ ι)‖ ≤
      ‖F‖ * ‖(WithLp.toLp 2 (fun i => G i j) : EuclideanSpace ℂ κ)‖ := h
  calc
    _ ≤ (‖F‖ * ‖(WithLp.toLp 2 (fun i => G i j) : EuclideanSpace ℂ κ)‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h' 2
    _ = _ := mul_pow _ _ _

end DirectCrouzeix

end

end OAI

-- ---- platform node ----
open OAI OAI.DirectCrouzeix
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open scoped MatrixOrder ComplexOrder


theorem solution : type_of% @_root_.OAI.DirectCrouzeix.hsSq_mul_le := @_root_.OAI.DirectCrouzeix.hsSq_mul_le
