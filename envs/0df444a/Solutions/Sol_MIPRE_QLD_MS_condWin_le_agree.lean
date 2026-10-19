-- Prove2me | solution 1 for MIPRE.QLD.MS.condWin_le_agree
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:30:40.840667+00:00
-- url     : https://prove2.me/submissions/43f4be7b-d995-4363-b7c9-fdd9653eebce

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (solution of MIPRE.QLD.MS.condWin_le_agree);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_QLD_MS_pvBit_rep
import Theorems.Thm_MIPRE_bornProb_nonneg

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.MS
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
variable {ψ : dA × dB → ℂ} {MA : layout.Question → POVM layout.Answer dA}
  {MB : layout.Question → POVM layout.Answer dB}
theorem _root_.solution (c : Fin layout.r) (j : Fin 3) :
    condWin nonlocalGame ψ MA MB (Sum.inl c) (Sum.inr (cell c j))
      ≤ ∑ d : layout.Answer, ∑ w : ZMod 2,
          (if pvBit c (rep c d) j = w then (1 : ℝ) else 0)
            * bornProb ψ (((MA (Sum.inl c)).mats d).val)
                (((MB (Sum.inr (cell c j))).mats (Sum.inr w)).val) := by
  rw [condWin]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [Fintype.sum_sum_type]
  have hzero : ∀ a' : Fin layout.s → ZMod 2,
      (if nonlocalGame.D (Sum.inl c) (Sum.inr (cell c j)) d (Sum.inl a') then (1 : ℝ) else 0)
        * bornProb ψ (((MA (Sum.inl c)).mats d).val)
            (((MB (Sum.inr (cell c j))).mats (Sum.inl a')).val) = 0 := by
    intro a'
    have : nonlocalGame.D (Sum.inl c) (Sum.inr (cell c j)) d (Sum.inl a') = false := by
      cases d <;> rfl
    rw [this, if_neg (by simp), zero_mul]
  rw [Finset.sum_congr rfl fun a' (_ : a' ∈ univ) => hzero a', Finset.sum_const_zero, zero_add]
  refine Finset.sum_le_sum fun w _ => ?_
  refine mul_le_mul_of_nonneg_right ?_
    (bornProb_nonneg ψ ((MA (Sum.inl c)).posSemidef d) ((MB _).posSemidef _))
  by_cases hacc : nonlocalGame.D (Sum.inl c) (Sum.inr (cell c j)) d (Sum.inr w)
  · rw [if_pos hacc]
    -- an accepted pair has Alice's answer parity-valid and agreeing with Bob's bit
    have hd : ∃ a : Fin layout.s → ZMod 2, d = Sum.inl a := by
      cases d with
      | inl a => exact ⟨a, rfl⟩
      | inr x => exact absurd hacc (by simp [nonlocalGame, Game.toNonlocalGame, Game.accepts])
    obtain ⟨a, rfl⟩ := hd
    have hacc' : (decide ((cell c j) ∈ layout.V c)
        && decide ((∑ k ∈ layout.V c, a k) = game.b c) && decide (a (cell c j) = w)) = true := by
      simpa [nonlocalGame, Game.toNonlocalGame, Game.accepts] using hacc
    have hpar : (∑ k ∈ layout.V c, a k) = game.b c := by
      simpa using (Bool.and_eq_true _ _ |>.mp (Bool.and_eq_true _ _ |>.mp hacc').1).2
    have hval : a (cell c j) = w := by
      simpa using (Bool.and_eq_true _ _ |>.mp hacc').2
    rw [if_pos (by rw [pvBit_rep c hpar j, hval])]
  · rw [if_neg hacc]
    split_ifs <;> norm_num
end MIPRE.QLD.MS
