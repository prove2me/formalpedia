-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.of_questions_diag
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:25:55.395691+00:00
-- url     : https://prove2.me/submissions/92d5d214-faa7-49eb-bc2c-5459d928fe16

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.of_questions_diag);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
/-- The canonical presentation, unfolded. -/
theorem through_eq {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    Line.through u z
      = (u - u (Fin.find (fun k => z k ≠ 0) hz) •
            ((z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z),
          (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z) := by
  rw [Line.through, dif_pos hz]
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [NeZero m] in
theorem _root_.solution {ℓ : Line F m} {u : Point F m} {s : Sample F m}
    (hℓ : ∃ k, ℓ.2 k ≠ 0)
    (hs : s.questions = ((Question.diagLine ℓ : Question F m), Question.point u)) :
    ∃ (j : Fin m) (v : Fin ((j : ℕ) + 1) → F), s = Sample.diag false u j v ∧
      ∃ c : F, c ≠ 0 ∧ (Sample.extend v : Point F m) = c • ℓ.2 := by
  classical
  match s, hs with
  | Sample.diag false u' j v, hs =>
      have hs' : ((Question.diagLine (Line.through u' (Sample.extend v)) : Question F m),
          Question.point u') = (Question.diagLine ℓ, Question.point u) := hs
      injection hs' with h1 h2
      injection h2 with hu
      subst hu
      injection h1 with hthr
      -- the direction cannot vanish, or the line's would too
      have hz : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := by
        by_contra hcon
        have h0 : (Sample.extend v : Point F m) = 0 :=
          funext fun k => not_not.mp fun hk => hcon ⟨k, hk⟩
        obtain ⟨k, hk⟩ := hℓ
        rw [h0, Line.through, dif_neg (by simp)] at hthr
        exact hk (by rw [← hthr]; simp)
      set p := Fin.find (fun k => (Sample.extend v : Point F m) k ≠ 0) hz with hp
      have hzp : (Sample.extend v : Point F m) p ≠ 0 := Fin.find_spec hz
      refine ⟨j, v, rfl, (Sample.extend v : Point F m) p, hzp, ?_⟩
      have hd : ℓ.2 = ((Sample.extend v : Point F m) p)⁻¹ • Sample.extend v := by
        rw [← hthr, through_eq hz]
      rw [hd, smul_smul, mul_inv_cancel₀ hzp, one_smul]
  | Sample.diag true u' j v, hs => exact absurd hs (by simp [Sample.questions])
  | Sample.axis false u' i, hs => exact absurd hs (by simp [Sample.questions])
  | Sample.axis true u' i, hs => exact absurd hs (by simp [Sample.questions])
  | Sample.selfConsistency u', hs => exact absurd hs (by simp [Sample.questions])
end MIPRE.LIDT.Adapter
