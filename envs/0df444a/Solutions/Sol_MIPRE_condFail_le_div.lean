-- Prove2me | solution 1 for MIPRE.condFail_le_div
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:32:25.181183+00:00
-- url     : https://prove2.me/submissions/91cf4742-d2a1-4c5e-9b1a-4cc0cc42d734

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (solution of MIPRE.condFail_le_div);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_POVMValue
import Theorems.Thm_MIPRE_POVM_posSemidef
import Theorems.Thm_MIPRE_bornProb_nonneg
import Theorems.Thm_MIPRE_sum_bornProb

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
theorem condWin_le_one (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    condWin G ψ MA MB x y ≤ 1 := by
  rw [← sum_bornProb hψ (MA x) (MB y)]
  refine Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => ?_
  have hb : 0 ≤ bornProb ψ (((MA x).mats a).val) (((MB y).mats b).val) :=
    bornProb_nonneg ψ ((MA x).posSemidef a) ((MB y).posSemidef b)
  by_cases h : G.D x y a b
  · rw [if_pos h, one_mul]
  · rw [if_neg h, zero_mul]
    exact hb
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem condFail_nonneg (hψ : star ψ ⬝ᵥ ψ = 1) (x : X) (y : Y) :
    0 ≤ condFail G ψ MA MB x y :=
  sub_nonneg.mpr (condWin_le_one hψ x y)
end
end MIPRE

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
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
theorem _root_.solution (hψ : star ψ ⬝ᵥ ψ = 1) {ε : ℝ} (hfail : 1 - povmValue G ψ MA MB ≤ ε)
    {x : X} {y : Y} (hμ : 0 < G.μ x y) :
    condFail G ψ MA MB x y ≤ ε / G.μ x y := by
  have hterm : G.μ x y * condFail G ψ MA MB x y ≤ ∑ x', ∑ y', G.μ x' y' * condFail G ψ MA MB x' y' := by
    refine le_trans ?_ (Finset.single_le_sum
      (f := fun x' => ∑ y', G.μ x' y' * condFail G ψ MA MB x' y') ?_ (Finset.mem_univ x))
    · exact Finset.single_le_sum
        (f := fun y' => G.μ x y' * condFail G ψ MA MB x y')
        (fun y' _ => mul_nonneg (G.μ_nonneg x y') (condFail_nonneg hψ x y')) (Finset.mem_univ y)
    · exact fun x' _ => Finset.sum_nonneg fun y' _ =>
        mul_nonneg (G.μ_nonneg x' y') (condFail_nonneg hψ x' y')
  rw [← one_sub_povmValue_eq] at hterm
  rw [le_div_iff₀ hμ, mul_comm]
  exact le_trans hterm hfail
end MIPRE
