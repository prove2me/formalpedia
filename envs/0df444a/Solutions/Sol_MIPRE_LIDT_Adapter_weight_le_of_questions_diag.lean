-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.weight_le_of_questions_diag
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:56.667431+00:00
-- url     : https://prove2.me/submissions/18c4b801-5f49-44dc-b776-ea5e60b80894

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.weight_le_of_questions_diag);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.DeriveFintype
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Background_LIDT_Game
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Background_LIDT_CLGame
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Weights
import Theorems.Thm_MIPRE_LIDT_Adapter_le_rev_diagIdx_of_questions
import Theorems.Thm_MIPRE_LIDT_Adapter_of_questions_diag

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution {ℓ : Line F m} (hℓ : ∃ k, ℓ.2 k ≠ 0) {u : Point F m}
    {s : Sample F m} (hsq : s.questions = ((Question.diagLine ℓ : Question F m),
      Question.point u)) :
    s.weight ≤ 1 / (6 * m * Fintype.card (Point F m) *
      (Fintype.card F : ℝ) ^ ((Fin.rev (diagIdx ℓ) : ℕ) + 1)) := by
  classical
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hmR : (0 : ℝ) < m := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m)
  have hP : (0 : ℝ) < Fintype.card (Point F m) := by exact_mod_cast Fintype.card_pos
  have hA : (0 : ℝ) < 6 * m * Fintype.card (Point F m) := by positivity
  have hden : (0 : ℝ) < 6 * m * Fintype.card (Point F m) *
      (Fintype.card F : ℝ) ^ ((Fin.rev (diagIdx ℓ) : ℕ) + 1) := mul_pos hA (pow_pos hq _)
  obtain ⟨j, v, hsj, _, _, _⟩ := of_questions_diag hℓ hsq
  subst hsj
  have hjge : ((Fin.rev (diagIdx ℓ) : ℕ)) ≤ (j : ℕ) := le_rev_diagIdx_of_questions hℓ hsq
  show 1 / (6 * m * Fintype.card (Point F m) * (Fintype.card F : ℝ) ^ ((j : ℕ) + 1)) ≤ _
  refine one_div_le_one_div_of_le hden ?_
  refine mul_le_mul_of_nonneg_left ?_ hA.le
  exact pow_le_pow_right₀ hq1 (by omega)
end MIPRE.LIDT.Adapter
