-- Prove2me | solution 1 for MIPRE.Introspection.unitaryTwirl_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:37:28.997769+00:00
-- url     : https://prove2.me/submissions/f478764e-bcfd-4ea6-8c43-9d35316b08fa

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/TwirlDistance.lean (solution of MIPRE.Introspection.unitaryTwirl_dist_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Theorems.Thm_MIPRE_quadForm_eq
import Theorems.Thm_MIPRE_stateSqNorm_avg_le

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
/-- The real form of `quadForm_eq`, which is how `def:state-distance` is written. -/
theorem stateSqNorm_eq (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M
      = (star ψ ⬝ᵥ ((((Mᴴ * M) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ)).re := by
  rw [quadForm_eq, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix
variable {dA dB I : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I]
/-- Left multiplication by an isometry preserves the state-dependent squared norm. -/
theorem stateSqNorm_mul_of_isometry (ψ : dA × dB → ℂ)
    (U M : Matrix dA dA ℂ) (hU : Uᴴ * U = 1) :
    stateSqNorm ψ (U * M) = stateSqNorm ψ M := by
  have h : (U * M)ᴴ * (U * M) = Mᴴ * M := by
    rw [Matrix.conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U M,
      hU, Matrix.one_mul]
  rw [stateSqNorm_eq, stateSqNorm_eq, h]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix
variable {dA dB I : Type*} [Fintype dA] [DecidableEq dA]
  [Fintype dB] [DecidableEq dB] [Fintype I]
theorem _root_.solution (μ : I → ℝ) (hμ0 : ∀ u, 0 ≤ μ u) (hμ1 : ∑ u, μ u = 1)
    (U : I → Matrix dA dA ℂ) (hU : ∀ u, (U u)ᴴ * U u = 1)
    (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ (unitaryTwirl μ U M - M) ≤
      ∑ u, μ u * stateSqNorm ψ (M * (U u)ᴴ - (U u)ᴴ * M) := by
  classical
  have hconst : (∑ u, (μ u : ℂ) • M) = M := by
    rw [← Finset.sum_smul, ← Complex.ofReal_sum, hμ1, Complex.ofReal_one, one_smul]
  have hJ := stateSqNorm_avg_le hμ0 hμ1 ψ
    (fun u => U u * M * (U u)ᴴ) (fun _ => M) (fun _ => 1) (by simp)
  simp only [mul_one, hconst] at hJ
  refine hJ.trans (le_of_eq ?_)
  unfold stateDist
  apply Finset.sum_congr rfl
  intro u _
  have hUU : U u * (U u)ᴴ = 1 := mul_eq_one_comm.mp (hU u)
  have hdiff : U u * M * (U u)ᴴ - M =
      U u * (M * (U u)ᴴ - (U u)ᴴ * M) := by
    rw [mul_sub, ← Matrix.mul_assoc (U u) (U u)ᴴ M, hUU, Matrix.one_mul,
      Matrix.mul_assoc]
  rw [hdiff, stateSqNorm_mul_of_isometry ψ _ _ (hU u)]
end MIPRE.Introspection
