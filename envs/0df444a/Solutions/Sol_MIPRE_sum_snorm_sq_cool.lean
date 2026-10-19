-- Prove2me | solution 1 for MIPRE.sum_snorm_sq_cool
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:21:38.393989+00:00
-- url     : https://prove2.me/submissions/f75a92ef-7f8d-4bb7-95cc-93daab7f1706

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (solution of MIPRE.sum_snorm_sq_cool);
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
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_CrossConsistency_B
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Commutation
import Theorems.Thm_MIPRE_IsPVM_nonneg
import Theorems.Thm_MIPRE_IsPVM_orthogonal

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_mulVec_sq {M : Type*} [Fintype M] (A : Matrix M N ℂ) (v : N → ℂ) :
    ‖evec (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [norm_evec_sq, star_mulVec_dotProduct]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_add (M M' : Matrix N N ℂ) : qform v (M + M') = qform v M + qform v M' := by
  rw [qform, qform, qform, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_sub (M M' : Matrix N N ℂ) : qform v (M - M') = qform v M - qform v M' := by
  rw [qform, qform, qform, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix N N ℂ) :
    qform v (∑ i ∈ s, f i) = ∑ i ∈ s, qform v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [qform]
  | insert i s hi ih => rw [Finset.sum_insert hi, qform_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem qform_nonneg_of_nonneg (v : N → ℂ) {Z : Matrix N N ℂ}
    (hZ : (0 : Matrix N N ℂ) ≤ Z) : 0 ≤ qform v Z := by
  have h := (Matrix.nonneg_iff_posSemidef.mp hZ).dotProduct_mulVec_nonneg v
  exact (Complex.nonneg_iff.mp h).1
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem qform_le_of_le (v : N → ℂ) {X Y : Matrix N N ℂ} (h : X ≤ Y) :
    qform v X ≤ qform v Y := by
  have h0 : 0 ≤ qform v (Y - X) := qform_nonneg_of_nonneg v (sub_nonneg.mpr h)
  rw [qform_sub] at h0
  linarith
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- **A contraction in front costs nothing.** The one-operator case of `sum_snorm_sq_mul_le`. -/
theorem snorm_sq_mul_le_of_contraction (v : N → ℂ) {P : Matrix N N ℂ}
    (hP : Pᴴ * P ≤ (1 : Matrix N N ℂ)) (M : Matrix N N ℂ) :
    snorm v (P * M) ^ 2 ≤ snorm v M ^ 2 := by
  rw [snorm_sq_eq_qform, snorm_sq_eq_qform, Matrix.conjTranspose_mul,
    show Mᴴ * Pᴴ * (P * M) = Mᴴ * (Pᴴ * P) * M from by noncomm_ring]
  refine qform_le_of_le v ?_
  have hpsd : (0 : Matrix N N ℂ) ≤ Mᴴ * ((1 : Matrix N N ℂ) - Pᴴ * P) * M :=
    Matrix.nonneg_iff_posSemidef.mpr
      ((Matrix.nonneg_iff_posSemidef.mp (sub_nonneg.mpr hP)).conjTranspose_mul_mul_same M)
  rw [show Mᴴ * ((1 : Matrix N N ℂ) - Pᴴ * P) * M = Mᴴ * M - Mᴴ * (Pᴴ * P) * M from by
    noncomm_ring] at hpsd
  exact sub_nonneg.mp hpsd
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
theorem _root_.solution {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (v : N → ℂ) {A : ι → Matrix N N ℂ} (hA : IsPVM A) (B : ι → Matrix N N ℂ) (f : ι → κ) :
    ∑ k : κ, snorm v (∑ i ∈ univ.filter fun i => f i = k, (A i - A i * B i)) ^ 2
      ≤ ∑ i, snorm v (A i - B i) ^ 2 := by
  classical
  have hterm : ∀ i, A i - A i * B i = A i * (A i - B i) := fun i => by
    rw [Matrix.mul_sub, hA.idem]
  have horth : ∀ i j : ι, i ≠ j →
      (A i * (A i - B i))ᴴ * (A j * (A j - B j)) = 0 := by
    intro i j hij
    rw [Matrix.conjTranspose_mul, hA.isSelfAdjoint,
      show (A i - B i)ᴴ * A i * (A j * (A j - B j))
          = (A i - B i)ᴴ * (A i * A j) * (A j - B j) from by noncomm_ring,
      hA.orthogonal hij, Matrix.mul_zero, Matrix.zero_mul]
  have hfib : ∀ k : κ, snorm v (∑ i ∈ univ.filter fun i => f i = k, (A i - A i * B i)) ^ 2
      = ∑ i ∈ univ.filter fun i => f i = k, snorm v (A i * (A i - B i)) ^ 2 := by
    intro k
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ.filter fun i => f i = k) => hterm i,
      snorm_sq_eq_qform, Matrix.conjTranspose_sum, Finset.sum_mul, qform_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Matrix.mul_sum, qform_sum, Finset.sum_eq_single_of_mem i hi fun j _ hji => ?_,
      snorm_sq_eq_qform]
    rw [horth i j (Ne.symm hji)]
    show qform v 0 = 0
    rw [qform, Matrix.zero_mulVec]
    simp
  rw [Finset.sum_congr rfl fun k (_ : k ∈ univ) => hfib k]
  refine le_trans (le_of_eq (Finset.sum_fiberwise (univ : Finset ι) f
    fun i => snorm v (A i * (A i - B i)) ^ 2)) (Finset.sum_le_sum fun i _ => ?_)
  refine snorm_sq_mul_le_of_contraction v ?_ _
  rw [hA.isSelfAdjoint, hA.idem]
  exact le_trans (Finset.single_le_sum (fun j _ => hA.nonneg j) (mem_univ i))
    (le_of_eq hA.sum_eq_one)
end MIPRE
