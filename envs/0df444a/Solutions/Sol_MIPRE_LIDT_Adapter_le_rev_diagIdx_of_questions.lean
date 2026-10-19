-- Prove2me | solution 1 for MIPRE.LIDT.Adapter.le_rev_diagIdx_of_questions
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:26:45.911125+00:00
-- url     : https://prove2.me/submissions/1885b4e2-6ca8-42ae-841d-0bcf4fa33216

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Weights.lean (solution of MIPRE.LIDT.Adapter.le_rev_diagIdx_of_questions);
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
import Theorems.Thm_MIPRE_LIDT_Adapter_of_questions_diag

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.Adapter
open Finset MIPRE.LIDT MIPRE.LIDT.CL
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ} [NeZero m]
omit [Fintype F] in
theorem _root_.solution {ℓ : Line F m} {u : Point F m} {j : Fin m}
    {v : Fin ((j : ℕ) + 1) → F} (hℓ : ∃ k, ℓ.2 k ≠ 0)
    (hs : (Sample.diag false u j v).questions
      = ((Question.diagLine ℓ : Question F m), Question.point u)) :
    ((Fin.rev (diagIdx ℓ) : ℕ)) ≤ (j : ℕ) := by
  classical
  obtain ⟨j', v', hjv, c, hc, hcv⟩ := of_questions_diag hℓ hs
  injection hjv with _ _ hj hv
  subst hj
  -- the line's direction vanishes above `j`
  have hvan : ∀ k : Fin m, (j : ℕ) < (k : ℕ) → ℓ.2 k = 0 := by
    intro k hk
    have hext : (Sample.extend v' : Point F m) k = 0 := by
      rw [Sample.extend, dif_neg (by omega)]
    have hprod : c * ℓ.2 k = 0 := by
      have h := congrFun hcv k
      rw [hext] at h
      simpa using h.symm
    rcases mul_eq_zero.mp hprod with h | h
    · exact absurd h hc
    · exact h
  -- so the reversed direction vanishes below `rev j`, and `diagIdx` is its first nonzero index
  have hex : ∃ k, (revPoint ℓ.2) k ≠ 0 := by
    obtain ⟨k, hk⟩ := hℓ
    exact ⟨Fin.rev k, by rwa [revPoint_apply, Fin.rev_rev]⟩
  have hmin : ∀ k : Fin m, (k : ℕ) < (Fin.rev j : ℕ) → (revPoint ℓ.2) k = 0 := by
    intro k hk
    rw [revPoint_apply]
    refine hvan _ ?_
    have h1 : (Fin.rev j : ℕ) = m - ((j : ℕ) + 1) := Fin.val_rev j
    have h2 : (Fin.rev k : ℕ) = m - ((k : ℕ) + 1) := Fin.val_rev k
    have := k.isLt
    have := j.isLt
    omega
  have hdi : diagIdx ℓ = Fin.find (fun k => (revPoint ℓ.2) k ≠ 0) hex := by
    rw [diagIdx, dif_pos hex]
  rw [hdi]
  set P := Fin.find (fun k => (revPoint ℓ.2) k ≠ 0) hex with hPdef
  by_contra hcon
  have hcon' : (j : ℕ) < ((Fin.rev P : Fin m) : ℕ) := Nat.lt_of_not_le hcon
  have h1 : ((Fin.rev P : Fin m) : ℕ) = m - ((P : ℕ) + 1) := Fin.val_rev P
  have h2 : ((Fin.rev j : Fin m) : ℕ) = m - ((j : ℕ) + 1) := Fin.val_rev j
  have h3 : (P : ℕ) < m := P.isLt
  have h4 : (j : ℕ) < m := j.isLt
  exact (Fin.find_spec hex) (hmin P (by omega))
end MIPRE.LIDT.Adapter
