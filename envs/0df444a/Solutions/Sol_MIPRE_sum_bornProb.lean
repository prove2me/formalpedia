-- Prove2me | solution 1 for MIPRE.sum_bornProb
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:49:00.035489+00:00
-- url     : https://prove2.me/submissions/0de9a7ad-753b-40c2-b0aa-3e53421fe3b8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/POVMValue.lean (solution of MIPRE.sum_bornProb);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.ENat.Lattice
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_POVMValue
import Theorems.Thm_MIPRE_POVM_sum_val

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem sum_quadForm {N ι : Type*} [Fintype N] (ψ : N → ℂ) (s : Finset ι)
    (f : ι → Matrix N N ℂ) :
    star ψ ⬝ᵥ ((∑ i ∈ s, f i) *ᵥ ψ) = ∑ i ∈ s, star ψ ⬝ᵥ ((f i) *ᵥ ψ) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_mulVec, dotProduct_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem kronecker_sum_right {dA dB ι : Type*} (M : Matrix dA dA ℂ) (s : Finset ι)
    (f : ι → Matrix dB dB ℂ) : M ⊗ₖ (∑ i ∈ s, f i) = ∑ i ∈ s, M ⊗ₖ f i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.kronecker_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
theorem sum_kronecker_left {dA dB ι : Type*} (s : Finset ι) (f : ι → Matrix dA dA ℂ)
    (N : Matrix dB dB ℂ) : (∑ i ∈ s, f i) ⊗ₖ N = ∑ i ∈ s, f i ⊗ₖ N := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_kronecker, ih, Finset.sum_insert hi]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (MA : POVM A dA)
    (MB : POVM B dB) :
    ∑ a, ∑ b, bornProb ψ (((MA.mats a).val)) (((MB.mats b).val)) = 1 := by
  classical
  have hker : ∑ a, ∑ b, (((MA.mats a).val) ⊗ₖ ((MB.mats b).val))
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
    have hb : ∀ a, ∑ b, (((MA.mats a).val) ⊗ₖ ((MB.mats b).val))
        = (((MA.mats a).val) ⊗ₖ (1 : Matrix dB dB ℂ)) := fun a => by
      rw [← kronecker_sum_right, POVM.sum_val]
    rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => hb a, ← sum_kronecker_left,
      POVM.sum_val, Matrix.one_kronecker_one]
  have h := sum_quadForm ψ (univ : Finset A)
    fun a => ∑ b, (((MA.mats a).val) ⊗ₖ ((MB.mats b).val))
  rw [hker, Matrix.one_mulVec, hψ] at h
  have h2 : ∀ a, (star ψ ⬝ᵥ ((∑ b, (((MA.mats a).val) ⊗ₖ ((MB.mats b).val))) *ᵥ ψ))
      = ∑ b, star ψ ⬝ᵥ ((((MA.mats a).val) ⊗ₖ ((MB.mats b).val)) *ᵥ ψ) :=
    fun a => sum_quadForm ψ _ _
  rw [Finset.sum_congr rfl fun a (_ : a ∈ univ) => h2 a] at h
  have h3 := congrArg Complex.re h
  rw [Complex.re_sum, Complex.one_re] at h3
  have hgoal : ∑ a, ∑ b, bornProb ψ (((MA.mats a).val)) (((MB.mats b).val))
      = ∑ a, (∑ b, star ψ ⬝ᵥ ((((MA.mats a).val) ⊗ₖ ((MB.mats b).val)) *ᵥ ψ)).re :=
    Finset.sum_congr rfl fun a _ => (Complex.re_sum _ _).symm
  rw [hgoal, ← h3]
end MIPRE
