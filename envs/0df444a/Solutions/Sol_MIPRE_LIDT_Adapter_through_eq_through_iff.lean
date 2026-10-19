-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.through_eq_through_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:28:38.153694+00:00
-- url     : https://prove2.me/submissions/6657a35d-1682-4bf9-8f17-0cd9cf426457

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Geometry.lean (solution of MIPRE.LIDT.Adapter.through_eq_through_iff);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

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
import Definitions.Def_MIPRE_Background_LIDT_Adapter_Geometry

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.LIDT.Adapter
section
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
/-- Scaling the direction does not move the first nonzero coordinate. -/
theorem find_smul {c : F} (hc : c ≠ 0) {w : Fin n → F}
    (hex : ∃ j, w j ≠ 0) (hex' : ∃ j, (c • w) j ≠ 0) :
    Fin.find (fun j => (c • w) j ≠ 0) hex' = Fin.find (fun j => w j ≠ 0) hex := by
  rw [Fin.find_eq_iff]
  refine ⟨?_, fun j hj => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul, ne_eq, mul_eq_zero, not_or]
    exact ⟨hc, Fin.find_spec hex⟩
  · have h0 : w j = 0 := not_not.mp (Fin.find_min hex hj)
    simp [h0]
end
end MIPRE.LIDT.Adapter

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
open Finset Submodule Module MIPRE.CL
variable {F : Type*} [Field F] {n : ℕ}
variable [DecidableEq F]
theorem _root_.solution {u w z : Fin n → F} (hw : ∃ k, w k ≠ 0) (hz : ∃ k, z k ≠ 0) :
    Line.through u z = Line.through u w ↔ ∃ c : F, c ≠ 0 ∧ z = c • w := by
  classical
  constructor
  · intro h
    set pz := Fin.find (fun k => z k ≠ 0) hz with hpz
    set pw := Fin.find (fun k => w k ≠ 0) hw with hpw
    have hzp : z pz ≠ 0 := Fin.find_spec hz
    have hwp : w pw ≠ 0 := Fin.find_spec hw
    have hdir : (z pz)⁻¹ • z = (w pw)⁻¹ • w := by
      have h2 := congrArg Prod.snd h
      rwa [through_eq hz, through_eq hw] at h2
    refine ⟨z pz * (w pw)⁻¹, mul_ne_zero hzp (inv_ne_zero hwp), ?_⟩
    have h4 : (z pz) • ((z pz)⁻¹ • z) = (z pz) • ((w pw)⁻¹ • w) := by rw [hdir]
    rw [smul_smul, mul_inv_cancel₀ hzp, one_smul, smul_smul] at h4
    exact h4
  · rintro ⟨c, hc, rfl⟩
    have hcw : ∃ k, (c • w) k ≠ 0 := by
      obtain ⟨k, hk⟩ := hw
      exact ⟨k, by simpa using mul_ne_zero hc hk⟩
    have hfind : Fin.find (fun k => (c • w) k ≠ 0) hcw
        = Fin.find (fun k => w k ≠ 0) hw := find_smul hc hw hcw
    have hwp : w (Fin.find (fun k => w k ≠ 0) hw) ≠ 0 := Fin.find_spec hw
    have hsame : ((c • w) (Fin.find (fun k => (c • w) k ≠ 0) hcw))⁻¹ • (c • w)
        = (w (Fin.find (fun k => w k ≠ 0) hw))⁻¹ • w := by
      rw [hfind]
      simp only [Pi.smul_apply, smul_eq_mul, smul_smul, mul_inv_rev]
      congr 1
      field_simp
    rw [through_eq hcw, through_eq hw, hsame, hfind]
end MIPRE.LIDT.Adapter
