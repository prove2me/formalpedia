-- Prove2me | solution 1 for MIPRE.Introspection.pvm_event_stability
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:23:49.828287+00:00
-- url     : https://prove2.me/submissions/29273005-25e0-4be0-a826-0e4a868b7278

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/ValueStability.lean (solution of MIPRE.Introspection.pvm_event_stability);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
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
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Linearity
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_Pasting
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Foundations_Introspection_ValueStability
import Theorems.Thm_MIPRE_Introspection_abs_sum_qform_mul_le

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
theorem qform_one [DecidableEq N] (hv : ‖evec v‖ = 1) : qform v (1 : Matrix N N ℂ) = 1 := by
  rw [qform, Matrix.one_mulVec, ← norm_evec_sq, hv, one_pow]
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

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
/-- A subset of the outcomes of a projective measurement has squared mass at most one. -/
theorem pvm_subset_mass (v : N → ℂ) (hv : ‖evec v‖ = 1)
    {M : C → Matrix N N ℂ} (hM : IsPVM M) (s : Finset C) :
    ∑ c ∈ s, snorm v (M c) ^ 2 ≤ 1 := by
  have hall : ∑ c, snorm v (M c) ^ 2 = 1 := by
    simp_rw [snorm_sq_eq_qform, hM.isSelfAdjoint, hM.idem]
    rw [← qform_sum, hM.sum_eq_one, qform_one v hv]
  rw [← hall]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N C : Type*} [Fintype N] [DecidableEq N] [Fintype C] [DecidableEq C]
theorem _root_.solution (v : N → ℂ) (hv : ‖evec v‖ = 1)
    {M R : C → Matrix N N ℂ} (hM : IsPVM M) (hR : IsPVM R)
    (s : Finset C) {δ : ℝ} (hd : ∑ c, snorm v (M c - R c) ^ 2 ≤ δ) :
    |(∑ c ∈ s, qform v (M c)) - ∑ c ∈ s, qform v (R c)| ≤ 2 * Real.sqrt δ := by
  have hδ : 0 ≤ δ := (sum_nonneg fun _ _ => sq_nonneg _).trans hd
  have hds : ∑ c ∈ s, snorm v (M c - R c) ^ 2 ≤ δ :=
    (sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ => sq_nonneg _)).trans hd
  have h1 : |∑ c ∈ s, qform v (M c * (M c - R c))| ≤ Real.sqrt δ := by
    refine (abs_sum_qform_mul_le v s M (fun c => M c - R c) hM.isSelfAdjoint).trans ?_
    calc
      _ ≤ Real.sqrt 1 * Real.sqrt δ := mul_le_mul
        (Real.sqrt_le_sqrt (pvm_subset_mass v hv hM s)) (Real.sqrt_le_sqrt hds)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, one_mul]
  have h2 : |∑ c ∈ s, qform v ((M c - R c) * R c)| ≤ Real.sqrt δ := by
    refine (abs_sum_qform_mul_le v s (fun c => M c - R c) R
      (fun c => by rw [conjTranspose_sub, hM.isSelfAdjoint, hR.isSelfAdjoint])).trans ?_
    calc
      _ ≤ Real.sqrt δ * Real.sqrt 1 := mul_le_mul (Real.sqrt_le_sqrt hds)
        (Real.sqrt_le_sqrt (pvm_subset_mass v hv hR s))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = _ := by rw [Real.sqrt_one, mul_one]
  have heq : (∑ c ∈ s, qform v (M c)) - ∑ c ∈ s, qform v (R c) =
      (∑ c ∈ s, qform v (M c * (M c - R c))) +
        ∑ c ∈ s, qform v ((M c - R c) * R c) := by
    rw [← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro c _
    rw [← qform_sub, ← qform_add]
    congr 1
    rw [mul_sub, sub_mul, hM.idem, hR.idem]
    abel
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)
end MIPRE.Introspection
