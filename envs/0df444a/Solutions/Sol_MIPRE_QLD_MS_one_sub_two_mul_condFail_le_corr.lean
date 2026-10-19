-- Prove2me | solution 1 for MIPRE.QLD.MS.one_sub_two_mul_condFail_le_corr
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:32:20.57899+00:00
-- url     : https://prove2.me/submissions/30c997e1-9214-4846-bc3b-fc180a6d8ab1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (solution of MIPRE.QLD.MS.one_sub_two_mul_condFail_le_corr);
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
import Theorems.Thm_MIPRE_QLD_MS_condWin_le_agree
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_sum_bornProb

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
theorem val_inj (x y : ZMod 2) (h : x.val = y.val) : x = y := by
  revert x y
  decide
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
theorem rsgn_mul_eq (x y : ZMod 2) :
    rsgn x * rsgn y = 2 * (if x = y then (1 : ℝ) else 0) - 1 := by
  have hx : x.val < 2 := ZMod.val_lt x
  have hy : y.val < 2 := ZMod.val_lt y
  have hiff : (x = y) ↔ (x.val = y.val) :=
    ⟨fun h => by rw [h], fun h => val_inj x y h⟩
  rw [rsgn, rsgn, show (if x = y then (1 : ℝ) else 0)
      = (if x.val = y.val then (1 : ℝ) else 0) from by
    by_cases h : x = y
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun hc => h (hiff.mpr hc))]]
  interval_cases h1 : x.val <;> interval_cases h2 : y.val <;> norm_num
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
variable {ψ : dA × dB → ℂ} {MA : layout.Question → POVM layout.Answer dA}
  {MB : layout.Question → POVM layout.Answer dB}
/-- The total Born mass on Bob's *bit* answers is at most one. -/
theorem sum_bornProb_inr_le (hψ : star ψ ⬝ᵥ ψ = 1) (c : Fin layout.r) (k : Fin layout.s) :
    ∑ d : layout.Answer, ∑ w : ZMod 2,
      bornProb ψ (((MA (Sum.inl c)).mats d).val) (((MB (Sum.inr k)).mats (Sum.inr w)).val)
      ≤ 1 := by
  rw [← sum_bornProb hψ (MA (Sum.inl c)) (MB (Sum.inr k))]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [Fintype.sum_sum_type]
  have h : (0 : ℝ) ≤ ∑ a' : Fin layout.s → ZMod 2,
      bornProb ψ (((MA (Sum.inl c)).mats d).val) (((MB (Sum.inr k)).mats (Sum.inl a')).val) :=
    Finset.sum_nonneg fun a' _ =>
      bornProb_nonneg ψ ((MA (Sum.inl c)).posSemidef d) ((MB (Sum.inr k)).posSemidef _)
  linarith
end
end MIPRE.QLD.MS

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
theorem _root_.solution (hψ : star ψ ⬝ᵥ ψ = 1) (c : Fin layout.r) (j : Fin 3) :
    1 - 2 * condFail nonlocalGame ψ MA MB (Sum.inl c) (Sum.inr (cell c j))
      ≤ corr ψ MA MB c j := by
  set q : layout.Answer → ZMod 2 → ℝ := fun d w =>
    bornProb ψ (((MA (Sum.inl c)).mats d).val)
      (((MB (Sum.inr (cell c j))).mats (Sum.inr w)).val) with hq
  have hexp : corr ψ MA MB c j
      = 2 * (∑ d : layout.Answer, ∑ w : ZMod 2,
            (if pvBit c (rep c d) j = w then (1 : ℝ) else 0) * q d w)
        - ∑ d : layout.Answer, ∑ w : ZMod 2, q d w := by
    rw [corr, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [rsgn_mul_eq]
    ring
  have hS := sum_bornProb_inr_le (MA := MA) (MB := MB) hψ c (cell c j)
  have hQ := condWin_le_agree (ψ := ψ) (MA := MA) (MB := MB) c j
  rw [hexp, condFail]
  linarith
end MIPRE.QLD.MS
