-- Prove2me | solution 1 for MIPRE.SyncStrategy.value_const
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-15T19:57:54.105153+00:00
-- url     : https://prove2.me/submissions/07e1eff4-8e8d-4fdf-92c4-11bffed0c6df

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/GameTransport.lean (solution of MIPRE.SyncStrategy.value_const);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_GameTransport

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.SyncStrategy
open Matrix Kronecker
open scoped ComplexOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable [DecidableEq A] {G : SynchronousGame X A}
theorem _root_.solution (G : SynchronousGame X A) (a₀ : A) :
    (const G a₀).value = ∑ x, ∑ y, G.μ x y * (if G.D x y a₀ a₀ then 1 else 0) := by
  rw [value_eq]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have hM : ∀ a b, ((const G a₀).P.M x a * (const G a₀).P.M y b).trace.re /
      ((const G a₀).d : ℝ) = if a = a₀ ∧ b = a₀ then 1 else 0 := by
    intro a b
    show ((if a = a₀ then (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) else 0) *
      (if b = a₀ then 1 else 0)).trace.re / ((const G a₀).d : ℝ) = _
    have hd : ((const G a₀).d : ℝ) = 1 := by simp [const]
    have h11 : (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) * 1 = 1 := mul_one 1
    have h10 : (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) * 0 = 0 := mul_zero 1
    have h01 : (0 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) * 1 = 0 := zero_mul 1
    have h00 : (0 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ) * 0 = 0 := mul_zero 0
    have htr : (1 : Matrix (Fin (const G a₀).d) (Fin (const G a₀).d) ℂ).trace = 1 := by
      rw [Matrix.trace_one, Fintype.card_fin]
      simp [const]
    split_ifs <;> simp_all
  simp_rw [hM]
  simp [Finset.sum_ite_eq', ite_and]
end MIPRE.SyncStrategy
