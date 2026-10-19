-- Prove2me | solution 1 for MIPRE.qform_sum_ge_of_close
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:30:26.570135+00:00
-- url     : https://prove2.me/submissions/32d183eb-094f-47d5-b95d-dd7553a76bb6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.qform_sum_ge_of_close);
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
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

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

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- **`X² ≤ X` for `0 ≤ X ≤ 1`**: `X - X² = X (1 - X)` is a product of commuting positive
matrices. -/
theorem mul_self_le_of_le_one {X : Matrix N N ℂ} (h0 : (0 : Matrix N N ℂ) ≤ X)
    (h1 : X ≤ (1 : Matrix N N ℂ)) : X * X ≤ X := by
  have hc : Commute X ((1 : Matrix N N ℂ) - X) := by
    show X * (1 - X) = (1 - X) * X
    noncomm_ring
  have hprod : (0 : Matrix N N ℂ) ≤ X * (1 - X) := hc.mul_nonneg h0 (sub_nonneg.mpr h1)
  have heq : X * ((1 : Matrix N N ℂ) - X) = X - X * X := by noncomm_ring
  rw [heq] at hprod
  exact sub_nonneg.mp hprod
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
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- An unweighted Cauchy--Schwarz, in the same shape. -/
theorem sum_mul_le_sqrt {ι : Type*} [Fintype ι] (u v : ι → ℝ) :
    ∑ i, u i * v i ≤ Real.sqrt (∑ i, u i ^ 2) * Real.sqrt (∑ i, v i ^ 2) := by
  have h := sum_weighted_mul_le_sqrt (fun _ : ι => (1 : ℝ)) u v fun _ => zero_le_one
  simpa using h
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
theorem inner_evec (u w : N → ℂ) : (inner ℂ (evec u) (evec w) : ℂ) = star u ⬝ᵥ w := by
  rw [evec, evec, EuclideanSpace.inner_toLp_toLp, dotProduct]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
/-- **Cauchy--Schwarz for a quadratic form.** The one estimate the chain uses, in the shape the
chain needs: the form of a product, split onto the two vectors. -/
theorem abs_qform_conjTranspose_mul_le (v : N → ℂ) (M P : Matrix N N ℂ) :
    |qform v (Mᴴ * P)| ≤ snorm v M * snorm v P := by
  have h : qform v (Mᴴ * P) = (inner ℂ (evec (M *ᵥ v)) (evec (P *ᵥ v)) : ℂ).re := by
    rw [qform, ← star_mulVec_dotProduct, inner_evec]
  rw [h]
  exact le_trans (Complex.abs_re_le_norm _) (norm_inner_le_norm _ _)
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N] {C : Type*} [Fintype C] [DecidableEq C]
theorem _root_.solution {v : N → ℂ} (hv : ‖evec v‖ = 1) {M P : C → Matrix N N ℂ}
    (hM : IsPVM M) (hP0 : ∀ c, (0 : Matrix N N ℂ) ≤ P c)
    (hPsum : ∑ c, P c ≤ (1 : Matrix N N ℂ))
    {δ : ℝ} (hclose : ∑ c, snorm v (M c - P c) ^ 2 ≤ δ) :
    1 - 2 * Real.sqrt δ ≤ ∑ c, qform v (P c) := by
  classical
  have hPsa : ∀ c, (P c)ᴴ = P c := fun c =>
    (Matrix.nonneg_iff_posSemidef.mp (hP0 c)).isHermitian
  have hP1 : ∀ c, P c ≤ (1 : Matrix N N ℂ) := fun c =>
    le_trans (Finset.single_le_sum (fun c' _ => hP0 c') (mem_univ c)) hPsum
  have hδ0 : 0 ≤ δ := le_trans (Finset.sum_nonneg fun c _ => sq_nonneg _) hclose
  -- the three mass sums
  have hMmass : ∑ c, snorm v (M c) ^ 2 = 1 := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [snorm_sq_eq_qform, hM.isSelfAdjoint c, hM.idem c], ← qform_sum, hM.sum_eq_one,
      qform_one v hv]
  have hPtotal : ∑ c, qform v (P c) ≤ 1 := by
    rw [← qform_sum, ← qform_one v hv]
    exact qform_le_of_le v hPsum
  have hPmass : ∑ c, snorm v (P c) ^ 2 ≤ 1 := by
    refine le_trans (Finset.sum_le_sum fun c _ => ?_) hPtotal
    rw [snorm_sq_eq_qform, hPsa c]
    exact qform_le_of_le v (mul_self_le_of_le_one (hP0 c) (hP1 c))
  -- the two Cauchy--Schwarz steps
  have hcs : ∀ (G : C → Matrix N N ℂ) (hG : ∀ c, (G c)ᴴ = G c) (K : C → Matrix N N ℂ),
      |∑ c, qform v (G c * K c)|
        ≤ Real.sqrt (∑ c, snorm v (G c) ^ 2) * Real.sqrt (∑ c, snorm v (K c) ^ 2) := by
    intro G hG K
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    refine le_trans (Finset.sum_le_sum fun c _ => ?_)
      (sum_mul_le_sqrt (fun c => snorm v (G c)) (fun c => snorm v (K c)))
    have h := abs_qform_conjTranspose_mul_le v (G c) (K c)
    rwa [hG c] at h
  have hstep1 : |∑ c, qform v (M c * (M c - P c))| ≤ Real.sqrt δ := by
    refine le_trans (hcs M hM.isSelfAdjoint (fun c => M c - P c)) ?_
    rw [hMmass, Real.sqrt_one, one_mul]
    exact Real.sqrt_le_sqrt hclose
  have hstep2 : |∑ c, qform v ((M c - P c) * P c)| ≤ Real.sqrt δ := by
    refine le_trans (hcs (fun c => M c - P c)
      (fun c => by rw [Matrix.conjTranspose_sub, hM.isSelfAdjoint c, hPsa c]) P) ?_
    calc Real.sqrt (∑ c, snorm v (M c - P c) ^ 2) * Real.sqrt (∑ c, snorm v (P c) ^ 2)
        ≤ Real.sqrt δ * Real.sqrt 1 :=
          mul_le_mul (Real.sqrt_le_sqrt hclose) (Real.sqrt_le_sqrt hPmass)
            (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = Real.sqrt δ := by rw [Real.sqrt_one, mul_one]
  -- unwinding the two identities
  have heq1 : ∑ c, qform v (M c * (M c - P c)) = 1 - ∑ c, qform v (M c * P c) := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [show M c * (M c - P c) = M c - M c * P c from by rw [Matrix.mul_sub, hM.idem c],
        qform_sub], Finset.sum_sub_distrib, ← qform_sum, hM.sum_eq_one, qform_one v hv]
  have heq2 : ∑ c, qform v ((M c - P c) * P c)
      = (∑ c, qform v (M c * P c)) - ∑ c, qform v (P c * P c) := by
    rw [Finset.sum_congr rfl fun c (_ : c ∈ univ) => by
      rw [Matrix.sub_mul, qform_sub], Finset.sum_sub_distrib]
  have hlow : 1 - 2 * Real.sqrt δ ≤ ∑ c, qform v (P c * P c) := by
    have h1 := (abs_le.mp hstep1).2
    have h2 := (abs_le.mp hstep2).2
    rw [heq1] at h1
    rw [heq2] at h2
    linarith
  refine le_trans hlow (Finset.sum_le_sum fun c _ => ?_)
  exact qform_le_of_le v (mul_self_le_of_le_one (hP0 c) (hP1 c))
end MIPRE
