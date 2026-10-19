-- Prove2me | solution 1 for MIPRE.LIDT.CL.one_sub_povmValue_clGame
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:28:07.604804+00:00
-- url     : https://prove2.me/submissions/75483356-0bd6-4d84-8438-238451c33edd

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/Adapter/Value.lean (solution of MIPRE.LIDT.CL.one_sub_povmValue_clGame);
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

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
/-- **The failure probability is the average of the conditional failures.** -/
theorem one_sub_povmValue_eq :
    1 - povmValue G ψ MA MB = ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y := by
  have h : ∑ x, ∑ y, G.μ x y * condFail G ψ MA MB x y
      = (∑ x, ∑ y, G.μ x y) - ∑ x, ∑ y, G.μ x y * condWin G ψ MA MB x y := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun y _ => by rw [condFail]; ring
  rw [h, G.μ_sum_one, povmValue]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.LIDT.CL
open Finset MIPRE
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {m d ldc : ℕ}
variable [NeZero m] (hm : m ∣ Fintype.card F)
theorem _root_.solution {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB]
    [DecidableEq dB] (ψ : dA × dB → ℂ) (MA : Question F m → POVM (Answer F m d ldc) dA)
    (MB : Question F m → POVM (Answer F m d ldc) dB) :
    1 - povmValue (clGame (d := d) (ldc := ldc) hm) ψ MA MB
      = (Fintype.card (Sample F m) : ℝ)⁻¹ * ∑ sm : Sample F m,
          condFail (clGame hm) ψ MA MB (sm.question hm sm.tyA) (sm.question hm sm.tyB) := by
  classical
  rw [one_sub_povmValue_eq, Finset.mul_sum]
  set c : ℝ := (Fintype.card (Sample F m) : ℝ)⁻¹ with hc
  set T : Question F m → Question F m → Sample F m → ℝ := fun x y sm =>
    (c * if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y) then 1 else 0)
      * condFail (clGame hm) ψ MA MB x y with hT
  have hμ : ∀ x y, (clGame (d := d) (ldc := ldc) hm).μ x y * condFail (clGame hm) ψ MA MB x y
      = ∑ sm : Sample F m, T x y sm := fun x y => by
    rw [hT]
    show (∑ sm : Sample F m, c * if (sm.question hm sm.tyA, sm.question hm sm.tyB) = (x, y)
      then (1 : ℝ) else 0) * condFail (clGame hm) ψ MA MB x y = _
    rw [Finset.sum_mul]
  simp only [hμ]
  calc ∑ x, ∑ y, ∑ sm, T x y sm
      = ∑ x, ∑ sm, ∑ y, T x y sm := Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = ∑ sm, ∑ x, ∑ y, T x y sm := Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun sm _ => ?_
  rw [← Fintype.sum_prod_type' fun x y => T x y sm]
  simp only [hT, mul_ite, mul_one, mul_zero, ite_mul, zero_mul, Prod.mk.eta, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]
end MIPRE.LIDT.CL
