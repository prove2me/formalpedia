-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.through_eq_through_revPoint
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:59.392753+00:00
-- url     : https://prove2.me/submissions/95eaad91-1eae-4db3-bf39-b989d7f7fb33

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.through_eq_through_revPoint);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_through_eq_through_iff

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

namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
/-- The canonical direction, projected out. -/
theorem through_snd {u z : Fin n → F} (hz : ∃ k, z k ≠ 0) :
    (Line.through u z).2 = (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ • z := by
  rw [through_eq hz]
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [NeZero m] in
theorem _root_.solution {u z w : Point F m} {c : F} (hc : c ≠ 0)
    (hz : ∃ k, z k ≠ 0)
    (h : c • (revPoint (Line.through u z).2 : Point F m) = w) :
    Line.through u z = Line.through u (revPoint w) := by
  classical
  have hzp : z (Fin.find (fun k => z k ≠ 0) hz) ≠ 0 := Fin.find_spec hz
  rw [through_snd hz, revPoint_smul, smul_smul] at h
  have hcz : c * (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹ ≠ 0 :=
    mul_ne_zero hc (inv_ne_zero hzp)
  have hrw : (revPoint w : Point F m)
      = (c * (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹) • z := by
    rw [← h, revPoint_smul, revPoint_revPoint]
  have hzeq : z = (c * (z (Fin.find (fun k => z k ≠ 0) hz))⁻¹)⁻¹ • (revPoint w : Point F m) := by
    rw [hrw, smul_smul, inv_mul_cancel₀ hcz, one_smul]
  have hwnz : ∃ k, (revPoint w : Point F m) k ≠ 0 := by
    refine ⟨Fin.find (fun k => z k ≠ 0) hz, ?_⟩
    rw [hrw]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hcz hzp
  exact (through_eq_through_iff hwnz hz).mpr ⟨_, inv_ne_zero hcz, hzeq⟩
end MIPRE.LIDT.Adapter
