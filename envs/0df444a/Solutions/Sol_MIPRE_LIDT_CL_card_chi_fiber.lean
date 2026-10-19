-- Prove2me | solution 1 for MIPRE.LIDT.CL.card_chi_fiber
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:30:25.718976+00:00
-- url     : https://prove2.me/submissions/b4f67ce8-047e-4e1d-b075-444a81e7c766

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/CLGame.lean (solution of MIPRE.LIDT.CL.card_chi_fiber);
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
import Theorems.Thm_MIPRE_LIDT_CL_card_div_pos
import Theorems.Thm_MIPRE_LIDT_CL_chi_val

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.CL
open Finset MIPRE.LIDT
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F] (m d ldc : ℕ)
variable {F m}
omit [DecidableEq F] in
theorem _root_.solution [NeZero m] (hm : m ∣ Fintype.card F) (i : Fin m) :
    #{s : F | chi hm s = i} = Fintype.card F / m := by
  classical
  have hc0 : 0 < Fintype.card F / m := card_div_pos hm
  have hmc : m * (Fintype.card F / m) = Fintype.card F := Nat.mul_div_cancel' hm
  rw [← Fintype.card_subtype]
  refine (Fintype.card_congr ?_).trans (Fintype.card_fin _)
  refine
    { toFun := fun s => ⟨(Fintype.equivFin F s).val % (Fintype.card F / m),
        Nat.mod_lt _ hc0⟩
      invFun := fun r => ⟨(Fintype.equivFin F).symm
        ⟨(i : ℕ) * (Fintype.card F / m) + (r : ℕ), ?_⟩, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · -- the index is below `q`
    have : (i : ℕ) + 1 ≤ m := i.isLt
    calc (i : ℕ) * (Fintype.card F / m) + (r : ℕ)
        < (i : ℕ) * (Fintype.card F / m) + (Fintype.card F / m) := by omega
      _ = ((i : ℕ) + 1) * (Fintype.card F / m) := by ring
      _ ≤ m * (Fintype.card F / m) := Nat.mul_le_mul_right _ this
      _ = Fintype.card F := hmc
  · -- it lands in the `i`-th block
    apply Fin.ext
    rw [chi_val]
    simp only [Equiv.apply_symm_apply]
    rw [mul_comm ((i : ℕ)) (Fintype.card F / m), Nat.mul_add_div hc0,
      Nat.div_eq_of_lt r.isLt, add_zero]
  · -- left inverse
    intro s
    obtain ⟨s, hs⟩ := s
    apply Subtype.ext
    apply (Fintype.equivFin F).injective
    simp only [Equiv.apply_symm_apply]
    apply Fin.ext
    have hdiv : (Fintype.equivFin F s).val / (Fintype.card F / m) = (i : ℕ) := by
      rw [← chi_val hm s, hs]
    have hdam := Nat.div_add_mod (Fintype.equivFin F s).val (Fintype.card F / m)
    rw [hdiv, mul_comm] at hdam
    exact hdam
  · -- right inverse
    intro r
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    rw [mul_comm ((i : ℕ)) (Fintype.card F / m), Nat.mul_add_mod,
      Nat.mod_eq_of_lt r.isLt]
end MIPRE.LIDT.CL
