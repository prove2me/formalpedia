-- Prove2me | solution 1 for MIPRE.LIDT.CL.rep_add_lineParam_smul
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:27:57.20792+00:00
-- url     : https://prove2.me/submissions/e36fe42f-fa45-43de-90ad-35c6d807d620

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Value.lean (solution of MIPRE.LIDT.CL.rep_add_lineParam_smul);
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
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Seeds
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Reparam
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Strategy
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Value
import Theorems.Thm_MIPRE_LIDT_Adapter_canonLin_bot
import Theorems.Thm_MIPRE_LIDT_Adapter_rep_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
/-- `CL.lineParam` recovers the parameter of a point on the line. -/
theorem lineParam_eq_of_mem {w : Fin n → F} (hw : ∃ j, w j ≠ 0) (u₀ : Fin n → F) (t : F) :
    CL.lineParam u₀ w (u₀ + t • w) = t := by
  simp only [CL.lineParam, dif_pos hw]
  set j := Fin.find (fun j => w j ≠ 0) hw with hj
  have hwj : w j ≠ 0 := Fin.find_spec hw
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_sub_cancel_left]
  exact mul_div_cancel_right₀ t hwj
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.CL
open Finset MIPRE
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}
omit [Fintype F] in
theorem _root_.solution (w u : Point F m) :
    rep w u + lineParam (rep w u) w u • w = u := by
  by_cases hw : ∃ j, w j ≠ 0
  · set c : F := u (Fin.find (fun j => w j ≠ 0) hw) / w (Fin.find (fun j => w j ≠ 0) hw) with hc
    have hu : u = rep w u + c • w := by
      rw [rep, Adapter.rep_eq hw u, sub_add_cancel]
    have hpar : lineParam (rep w u) w u = c := by
      have h := Adapter.lineParam_eq_of_mem hw (rep w u) c
      rwa [← hu] at h
    rw [hpar]
    exact hu.symm
  · have hw0 : w = 0 := funext fun j => not_not.mp fun h => hw ⟨j, h⟩
    subst hw0
    rw [smul_zero, add_zero, rep, Set.singleton_zero, Submodule.span_zero, Adapter.canonLin_bot]
end MIPRE.LIDT.CL
