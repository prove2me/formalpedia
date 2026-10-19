-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.eq_diag_zero_of_qmapS
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:29:39.398024+00:00
-- url     : https://prove2.me/submissions/f7c15807-9644-41f7-882d-34d9347b122c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.eq_diag_zero_of_qmapS);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_exists_diag_of_qmapS_dline

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
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] [DecidableEq F] [NeZero m] in
/-- `Sample.extend` is the extension by zero, so it recovers `v` on `v`'s own indices. -/
theorem extend_apply_coe {j : Fin m} (v : Fin ((j : ℕ) + 1) → F) (i : Fin ((j : ℕ) + 1)) :
    (Sample.extend v : Point F m)
        ⟨(i : ℕ), lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) j.isLt⟩ = v i := by
  rw [Sample.extend, dif_pos (Nat.le_of_lt_succ i.isLt)]
end
end MIPRE.LIDT.Adapter

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
theorem _root_.solution (hm : m ∣ Fintype.card F) (σc : Seed F m)
    {u₀ : Point F m} {s₀ : F} {yp : Point F m} {s : Sample F m}
    (h1 : qmapS hm σc s.questions.1 = CL.Question.dline u₀ s₀ 0)
    (h2 : qmapS hm σc s.questions.2 = CL.Question.point yp) :
    ∃ j : Fin m, s = Sample.diag false (revPoint yp) j (0 : Fin ((j : ℕ) + 1) → F) := by
  classical
  obtain ⟨j, v, rfl⟩ := exists_diag_of_qmapS_dline hm σc h1 h2
  refine ⟨j, ?_⟩
  -- the scale is nonzero, so the reversed direction vanishes, so the direction does
  set ℓ : Line F m := Line.through (revPoint yp) (Sample.extend v) with hℓ
  have h1' : (CL.Question.dline (revPoint ℓ.1 - shiftOf ℓ • revPoint ℓ.2)
      (seedOf hm (diagIdx ℓ) (σc.1 (diagIdx ℓ))) ((σc.2 : F) • revPoint ℓ.2)
      : CL.Question F m) = CL.Question.dline u₀ s₀ 0 := h1
  have hdir : (σc.2 : F) • (revPoint ℓ.2 : Point F m) = 0 := (CL.Question.dline.inj h1').2.2
  have hrev : (revPoint ℓ.2 : Point F m) = 0 :=
    (smul_eq_zero.mp hdir).resolve_left σc.2.2
  have hℓ2 : (ℓ.2 : Point F m) = 0 := by
    have := congrArg revPoint hrev
    rwa [revPoint_revPoint, revPoint_zero] at this
  -- a canonical presentation has zero direction only for a zero input direction
  have hext : (Sample.extend v : Point F m) = 0 := by
    by_contra hne
    obtain ⟨k, hk⟩ : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := by
      by_contra hall
      exact hne (funext fun k => not_not.mp fun hc => hall ⟨k, hc⟩)
    have hex : ∃ k, (Sample.extend v : Point F m) k ≠ 0 := ⟨k, hk⟩
    have hp : (Sample.extend v : Point F m)
        (Fin.find (fun k => (Sample.extend v : Point F m) k ≠ 0) hex) ≠ 0 := Fin.find_spec hex
    have h2' : (ℓ.2 : Point F m)
        = ((Sample.extend v : Point F m)
            (Fin.find (fun k => (Sample.extend v : Point F m) k ≠ 0) hex))⁻¹
          • (Sample.extend v : Point F m) := by
      rw [hℓ, through_eq hex]
    rw [hℓ2] at h2'
    have := congrFun h2' (Fin.find (fun k => (Sample.extend v : Point F m) k ≠ 0) hex)
    simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hp] at this
    exact zero_ne_one this
  have hv : v = 0 := by
    funext i
    have hi := congrFun hext ⟨(i : ℕ), lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) j.isLt⟩
    rw [extend_apply_coe] at hi
    exact hi
  rw [hv]
end MIPRE.LIDT.Adapter
