-- Prove2me | solution 1 for MIPRE.xStateDist_obsOf_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:22:26.115405+00:00
-- url     : https://prove2.me/submissions/4d2e60a3-d635-4aa6-b2ee-057293f18176

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (solution of MIPRE.xStateDist_obsOf_le);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Theorems.Thm_MIPRE_sq_sum_le_card_mul_sum_sq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateVec_sum {ι : Type*} (ψ : dA × dB → ℂ) (s : Finset ι) (f : ι → Matrix dA dA ℂ) :
    stateVec ψ (∑ i ∈ s, f i) = ∑ i ∈ s, stateVec ψ (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.sum_insert hi, stateVec_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
variable [DecidableEq dA]
omit [DecidableEq dB] in
theorem stateVecB_sum {ι : Type*} (ψ : dA × dB → ℂ) (t : Finset ι) (f : ι → Matrix dB dB ℂ) :
    stateVecB ψ (∑ i ∈ t, f i) = ∑ i ∈ t, stateVecB ψ (f i) := by
  classical
  induction t using Finset.induction with
  | empty => simp [stateVecB]
  | insert i t hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih, stateVecB, stateVecB, stateVecB,
        Matrix.kronecker_add, Matrix.add_mulVec]
      rfl
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [DecidableEq C] in
theorem _root_.solution {μ : X → ℝ} (hμ0 : ∀ x, 0 ≤ μ x) (ψ : dA × dB → ℂ)
    (M : X → POVM C dA) (N : X → POVM C dB) (α : C → ℂ) (hα : ∀ a, ‖α a‖ ≤ 1) :
    xStateDist μ ψ (obsOf α M) (obsOf α N)
      ≤ (Fintype.card C : ℝ) * xPovmDist μ ψ M N := by
  classical
  rw [xPovmDist, Finset.mul_sum, xStateDist]
  refine Finset.sum_le_sum fun x _ => ?_
  rw [← mul_assoc, mul_comm ((Fintype.card C : ℝ)) (μ x), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (hμ0 x)
  have hsub : stateVec ψ (obsOf α M x) - stateVecB ψ (obsOf α N x)
      = ∑ a, α a • (stateVec ψ (((M x).mats a).val) - stateVecB ψ (((N x).mats a).val)) := by
    rw [obsOf, obsOf, stateVec_sum, stateVecB_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun a _ => by
      rw [stateVec_smul, stateVecB_smul, smul_sub]
  have htri : ‖stateVec ψ (obsOf α M x) - stateVecB ψ (obsOf α N x)‖
      ≤ ∑ a, ‖stateVec ψ (((M x).mats a).val) - stateVecB ψ (((N x).mats a).val)‖ := by
    rw [hsub]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
    rw [norm_smul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hα a)
  calc xSqNorm ψ (obsOf α M x) (obsOf α N x)
      ≤ (∑ a, ‖stateVec ψ (((M x).mats a).val) - stateVecB ψ (((N x).mats a).val)‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) htri 2
    _ ≤ (Fintype.card C : ℝ)
          * ∑ a, ‖stateVec ψ (((M x).mats a).val) - stateVecB ψ (((N x).mats a).val)‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq _ fun a => norm_nonneg _
    _ = (Fintype.card C : ℝ) * ∑ a, xSqNorm ψ (((M x).mats a).val) (((N x).mats a).val) := rfl
end MIPRE
