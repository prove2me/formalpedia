-- Prove2me | solution 1 for MIPRE.Repeat.DecAcc_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:48:46.243478+00:00
-- url     : https://prove2.me/submissions/ad0b8ae7-f89b-446e-8775-8a4bedd6ba3e

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Repeat/RepDecider.lean (solution of MIPRE.Repeat.DecAcc_iff);
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
import Definitions.Def_MIPRE_Foundations_Cost_Kleene_B
import Definitions.Def_MIPRE_Foundations_Repeat_DecLoop
import Definitions.Def_MIPRE_Foundations_Halting_Serial
import Definitions.Def_MIPRE_Foundations_Repeat_DecMain
import Definitions.Def_MIPRE_Foundations_Repeat_RepDecider
import Theorems.Thm_MIPRE_Cost_Prog_okBits_iff

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Cost.Data (chunk)
variable {k s : ℕ}
theorem chunk_succ {α : Type*} (i : ℕ) (l : List α) : chunk s (i + 1) l = chunk s i (l.drop s) := by
  simp only [chunk, List.drop_drop]
  congr 2
  ring
end
end MIPRE.CL

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Repeat
open Cost Cost.Data Cost.Prog CL
variable {ℓ : ℕ} (S : CL.Sampler ℓ) (D : Decider)
theorem _root_.solution (univ : Prog) (dD nD : Data) (s B : ℕ) :
    ∀ (k : ℕ) (remX remY remA remB : List Data),
      DecAcc univ dD nD s B k remX remY remA remB ↔
        ∃ aa bb : Fin k → BitStr,
          remA = List.ofFn (fun i => encode (aa i)) ∧ remB = List.ofFn (fun i => encode (bb i)) ∧
          ∀ i, (aa i).length ≤ B ∧ (bb i).length ≤ B ∧
            ∃ t, Eval [decQuery dD nD (list (chunk s i remX)) (list (chunk s i remY))
              (encode (aa i)) (encode (bb i))] univ (.cons .nil .nil) t
  | 0, remX, remY, remA, remB => by
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨fun i => i.elim0, fun i => i.elim0, by simp, by simp, fun i => i.elim0⟩
    · rintro ⟨aa, bb, rfl, rfl, -⟩
      exact ⟨by simp, by simp⟩
  | k + 1, remX, remY, [], remB => by
    constructor
    · intro h; exact h.elim
    · rintro ⟨aa, bb, h, -, -⟩
      simp [List.ofFn_succ] at h
  | k + 1, remX, remY, _ :: _, [] => by
    constructor
    · intro h; exact h.elim
    · rintro ⟨aa, bb, -, h, -⟩
      simp [List.ofFn_succ] at h
  | k + 1, remX, remY, ai :: remA', bi :: remB' => by
    constructor
    · rintro ⟨hoka, hokb, hcall, hrec⟩
      obtain ⟨a₀, rfl, ha₀⟩ := (okBits_iff B ai).mp hoka
      obtain ⟨b₀, rfl, hb₀⟩ := (okBits_iff B bi).mp hokb
      obtain ⟨aa, bb, rfl, rfl, hall⟩ := (solution univ dD nD s B k _ _ remA' remB').mp hrec
      refine ⟨Fin.cons a₀ aa, Fin.cons b₀ bb, ?_, ?_, ?_⟩
      · simp [List.ofFn_succ]
      · simp [List.ofFn_succ]
      · intro i
        refine Fin.cases ?_ (fun i' => ?_) i
        · simpa [chunk_zero] using ⟨ha₀, hb₀, hcall⟩
        · simpa [chunk_succ] using hall i'
    · rintro ⟨aa, bb, hA, hB, hall⟩
      simp only [List.ofFn_succ, List.cons.injEq] at hA hB
      obtain ⟨rfl, rfl⟩ := hA
      obtain ⟨rfl, rfl⟩ := hB
      obtain ⟨ha₀, hb₀, hcall⟩ := hall 0
      refine ⟨(okBits_iff B _).mpr ⟨_, rfl, ha₀⟩, (okBits_iff B _).mpr ⟨_, rfl, hb₀⟩,
        by simpa [chunk_zero] using hcall, ?_⟩
      refine (solution univ dD nD s B k _ _ _ _).mpr ⟨fun i => aa i.succ, fun i => bb i.succ, rfl, rfl,
        fun i => ?_⟩
      simpa [chunk_succ] using hall i.succ
end MIPRE.Repeat
