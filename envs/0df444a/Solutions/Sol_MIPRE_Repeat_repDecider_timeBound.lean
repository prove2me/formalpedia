-- Prove2me | solution 1 for MIPRE.Repeat.repDecider_timeBound
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:54:16.173987+00:00
-- url     : https://prove2.me/submissions/66479770-299f-4db7-a291-da9742ab92fa

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/DeciderCost.lean (solution of MIPRE.Repeat.repDecider_timeBound);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Computability.Primrec.List
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Bits
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Logic.Denumerable
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Basic
import Definitions.Def_MIPRE_Foundations_CL_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Basic_B
import Definitions.Def_MIPRE_Foundations_Cost_Encoding_B
import Definitions.Def_MIPRE_Foundations_Cost_PolyTime
import Definitions.Def_MIPRE_Foundations_CL_Sampler
import Definitions.Def_MIPRE_Foundations_Verifier
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_GapCompression
import Definitions.Def_MIPRE_Foundations_VerifierValue
import Definitions.Def_MIPRE_Foundations_Pipeline_Budget
import Definitions.Def_MIPRE_Foundations_Pipeline_Repetition
import Definitions.Def_MIPRE_Foundations_Cost_Closure
import Definitions.Def_MIPRE_Foundations_Cost_Loops_B
import Definitions.Def_MIPRE_Foundations_Cost_Codable_B
import Definitions.Def_MIPRE_Foundations_Halting_Descriptions
import Definitions.Def_MIPRE_Foundations_Cost_Unary
import Definitions.Def_MIPRE_Foundations_Cost_Numeric_B
import Definitions.Def_MIPRE_Foundations_Halting_Lists
import Definitions.Def_MIPRE_Foundations_Halting_Lists_B
import Definitions.Def_MIPRE_Foundations_Cost_Growth
import Definitions.Def_MIPRE_Foundations_Halting_Arith
import Definitions.Def_MIPRE_Foundations_Repeat_Prims
import Definitions.Def_MIPRE_Foundations_Repeat_MapLoop
import Definitions.Def_MIPRE_Foundations_Cost_Toolkit_B
import Definitions.Def_MIPRE_Foundations_Repeat_Sampler
import Definitions.Def_MIPRE_Foundations_CL_Repeat
import Definitions.Def_MIPRE_Foundations_Repeat_Bits
import Definitions.Def_MIPRE_Foundations_Cost_Machine_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineData_B
import Definitions.Def_MIPRE_Foundations_Cost_Interpreter_B
import Definitions.Def_MIPRE_Foundations_Cost_MachineBound_B
import Definitions.Def_MIPRE_Foundations_Cost_Universal_B
import Definitions.Def_MIPRE_Foundations_Repeat_RepSampler
import Definitions.Def_MIPRE_Foundations_Repeat_Dom
import Definitions.Def_MIPRE_Foundations_Repeat_SamplerCost
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Definitions.Def_MIPRE_Foundations_Repeat_RepDecider
import Definitions.Def_MIPRE_Foundations_Repeat_DeciderCost
import Theorems.Thm_MIPRE_Repeat_decMalformed_time
import Theorems.Thm_MIPRE_Repeat_decWellformed_time

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem le {c m e v : ℕ} (h : Dom W X K c m e v) : v ≤ c * (W + 1) ^ m * X ^ (e * (K + 1)) := h
end
end MIPRE.Repeat.Dom

namespace MIPRE.Repeat.Dom
section
variable {W X K : ℕ}
theorem mono (hX : 1 ≤ X) {c c' m m' e e' v : ℕ} (h : Dom W X K c m e v) (hc : c ≤ c') (hm : m ≤ m')
    (he : e ≤ e') : Dom W X K c' m' e' v := by
  unfold Dom at h ⊢
  refine h.trans ?_
  gcongr <;> first | omega | exact Nat.mul_le_mul_right _ he
end
end MIPRE.Repeat.Dom

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
theorem _root_.solution : ∃ c m e, ∀ {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
    (lam tau beta n : ℕ) (R : Budget) (W : ℕ), DecDom S D lam tau beta n R W →
    S.TimeBoundAt n R.S R.k → D.TimeBoundAt n R.D R.k →
    (repDecider S.prog D.prog lam tau beta).TimeBoundAt n (c * (W + 1) ^ m) (e * (R.k + 1)) := by
  obtain ⟨c₁, m₁, e₁, h₁⟩ := decMalformed_time
  obtain ⟨c₂, m₂, e₂, h₂⟩ := decWellformed_time
  refine ⟨c₁ + c₂, max m₁ m₂, max e₁ e₂, fun {ℓ} S D lam tau beta n R W hW hS hD d => ?_⟩
  have hX : 1 ≤ d.size + 1 := by omega
  rcases d with _ | ⟨xD, _ | ⟨yD, _ | ⟨aD, bD⟩⟩⟩
  · obtain ⟨r, t, ht, run⟩ := h₁ S D lam tau beta n R W .nil hW (Or.inl rfl)
    exact ⟨r, t, (Dom.mono hX ht (by omega) (le_max_left _ _) (le_max_left _ _)).le, run⟩
  · obtain ⟨r, t, ht, run⟩ := h₁ S D lam tau beta n R W _ hW (Or.inr (Or.inl ⟨xD, rfl⟩))
    exact ⟨r, t, (Dom.mono hX ht (by omega) (le_max_left _ _) (le_max_left _ _)).le, run⟩
  · obtain ⟨r, t, ht, run⟩ := h₁ S D lam tau beta n R W _ hW (Or.inr (Or.inr ⟨xD, yD, rfl⟩))
    exact ⟨r, t, (Dom.mono hX ht (by omega) (le_max_left _ _) (le_max_left _ _)).le, run⟩
  · obtain ⟨r, t, ht, run⟩ := h₂ S D lam tau beta n R W xD yD aD bD hW hS hD
    exact ⟨r, t, (Dom.mono hX ht (by omega) (le_max_right _ _) (le_max_right _ _)).le, run⟩
end MIPRE.Repeat
