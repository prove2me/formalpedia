-- Prove2me | solution 1 for MIPRE.sum_stateSqNorm_le_one
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:54:18.438435+00:00
-- url     : https://prove2.me/submissions/5780a9ba-c12f-4f46-9af6-2491399647bb

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (solution of MIPRE.sum_stateSqNorm_le_one);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_quadForm_eq

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
theorem sum_kronecker_left {dA dB ι : Type*} (s : Finset ι) (f : ι → Matrix dA dA ℂ)
    (N : Matrix dB dB ℂ) : (∑ i ∈ s, f i) ⊗ₖ N = ∑ i ∈ s, f i ⊗ₖ N := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Matrix.add_kronecker, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
/-- Each POVM element is at most the identity. -/
theorem POVM.le_one {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d] (M : POVM A d)
    (p : A) : ((M.mats p).val) ≤ (1 : Matrix d d ℂ) := by
  rw [← POVM.sum_val M]
  exact Finset.single_le_sum (fun a _ => Subtype.coe_le_coe.mpr (M.nonneg a)) (Finset.mem_univ p)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- `A² ≤ A` for a POVM element: `A^{1/2}(1 - A)A^{1/2} ≥ 0`, here through the commuting
product `A * (1 - A)`. -/
theorem POVM.mul_self_le_self (M : POVM A dA) (a : A) :
    ((M.mats a).val) * ((M.mats a).val) ≤ ((M.mats a).val) := by
  set P := ((M.mats a).val) with hP
  have h0 : (0 : Matrix dA dA ℂ) ≤ P := Subtype.coe_le_coe.mpr (M.nonneg a)
  have h1 : (0 : Matrix dA dA ℂ) ≤ 1 - P := sub_nonneg.mpr (M.le_one a)
  have hc : Commute P (1 - P) := by show P * (1 - P) = (1 - P) * P; noncomm_ring
  have hprod : (0 : Matrix dA dA ℂ) ≤ P * (1 - P) := hc.mul_nonneg h0 h1
  have heq : P * ((1 : Matrix dA dA ℂ) - P) = P - P * P := by noncomm_ring
  rw [heq] at hprod
  exact sub_nonneg.mp hprod
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
omit [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB]
  [DecidableEq dB] in
/-- A difference in the left factor of a Kronecker product splits off. -/
theorem sub_kronecker_right (N P : Matrix dA dA ℂ) (R : Matrix dB dB ℂ) :
    (N - P) ⊗ₖ R = N ⊗ₖ R - P ⊗ₖ R := by
  ext p q
  simp only [Matrix.sub_apply, Matrix.kroneckerMap_apply]
  ring
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (M : POVM A dA) :
    ∑ a, stateSqNorm ψ (((M.mats a).val)) ≤ 1 := by
  classical
  have hterm : ∀ a, (stateSqNorm ψ (((M.mats a).val)) : ℝ)
      ≤ (star ψ ⬝ᵥ ((((M.mats a).val) ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ)).re := by
    intro a
    have hsa : (((M.mats a).val))ᴴ = ((M.mats a).val) := by
      rw [← Matrix.star_eq_conjTranspose, (M.mats a).2]
    have hdiff : (0 : Matrix dA dA ℂ)
        ≤ ((M.mats a).val) - (((M.mats a).val))ᴴ * ((M.mats a).val) := by
      rw [hsa]; exact sub_nonneg.mpr (POVM.mul_self_le_self M a)
    have hker : (0 : Matrix (dA × dB) (dA × dB) ℂ)
        ≤ (((M.mats a).val) - (((M.mats a).val))ᴴ * ((M.mats a).val))
            ⊗ₖ (1 : Matrix dB dB ℂ) :=
      Matrix.nonneg_iff_posSemidef.mpr
        ((Matrix.nonneg_iff_posSemidef.mp hdiff).kronecker
          (Matrix.PosSemidef.one : (1 : Matrix dB dB ℂ).PosSemidef))
    have hq := (Matrix.nonneg_iff_posSemidef.mp hker).dotProduct_mulVec_nonneg ψ
    rw [sub_kronecker_right, Matrix.sub_mulVec, dotProduct_sub, quadForm_eq] at hq
    have := (Complex.nonneg_iff.mp hq).1
    simp only [Complex.sub_re, Complex.ofReal_re] at this
    linarith
  refine (Finset.sum_le_sum fun a _ => hterm a).trans ?_
  have hsum : ∑ a, (star ψ ⬝ᵥ ((((M.mats a).val) ⊗ₖ (1 : Matrix dB dB ℂ)) *ᵥ ψ)).re
      = (star ψ ⬝ᵥ ((∑ a, (((M.mats a).val) ⊗ₖ (1 : Matrix dB dB ℂ))) *ᵥ ψ)).re := by
    rw [sum_quadForm ψ (univ : Finset A) fun a => (((M.mats a).val) ⊗ₖ
      (1 : Matrix dB dB ℂ)), Complex.re_sum]
  rw [hsum, ← sum_kronecker_left, POVM.sum_val, Matrix.one_kronecker_one, Matrix.one_mulVec,
    hψ, Complex.one_re]
end MIPRE
