-- Prove2me | solution 1 for MIPRE.one_sub_sum_bornProb_sand_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:34:53.474988+00:00
-- url     : https://prove2.me/submissions/deff5776-a876-4ab9-9103-5c6ee64812f2

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sandwich.lean (solution of MIPRE.one_sub_sum_bornProb_sand_le);
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
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_abs_link1_le
import Theorems.Thm_MIPRE_abs_link2_le
import Theorems.Thm_MIPRE_abs_link3_le
import Theorems.Thm_MIPRE_norm_stateVecB
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_eq
import Theorems.Thm_MIPRE_sum_stateSqNorm_le_one
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt
import Theorems.Thm_MIPRE_swapVec_dotProduct

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
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_add (X Y : Matrix HB HB ℂ) :
    bOp (X + Y) = (bOp X : Matrix (HA × HB) _ ℂ) + bOp Y := Matrix.kronecker_add _ _ _
end
end MIPRE

namespace MIPRE
section
open Finset Matrix Kronecker
variable {X : Type*} [Fintype X]
variable {dA dB : Type*} [Fintype dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_nonneg (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) : 0 ≤ stateSqNorm ψ M :=
  sq_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem xSqNorm_nonneg (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    0 ≤ xSqNorm ψ A B := by rw [xSqNorm]; positivity
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- Bob's version, by the swap. -/
theorem sum_stateSqNormB_le_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (N : POVM B dB) :
    ∑ b, ‖stateVecB ψ (((N.mats b).val))‖ ^ 2 ≤ 1 := by
  have hψ' : star (swapVec ψ) ⬝ᵥ swapVec ψ = 1 := by rw [swapVec_dotProduct]; exact hψ
  have h := sum_stateSqNorm_le_one (dA := dB) (dB := dA) (A := B) hψ' N
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun b _ => ?_)) h
  rw [norm_stateVecB, stateSqNorm]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
omit [DecidableEq dA] in
theorem norm_stateVec_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) :
    ‖stateVec ψ A‖ = snorm ψ (aOp A : Matrix (dA × dB) _ ℂ) := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bOp_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix dB dB ℂ) :
    bOp (∑ i ∈ s, f i) = ∑ i ∈ s, (bOp (f i) : Matrix (dA × dB) _ ℂ) := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty, bOp, Matrix.kronecker_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, bOp_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- **Moving an average inside a square root.** Cauchy--Schwarz against the constant one. -/
theorem sum_weighted_sqrt_le {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hf : ∀ i, 0 ≤ f i) :
    ∑ i, w i * Real.sqrt (f i) ≤ Real.sqrt (∑ i, w i * f i) := by
  have h := sum_weighted_mul_le_sqrt w (fun i => Real.sqrt (f i)) (fun _ => (1 : ℝ)) hw0
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * (Real.sqrt (f i) * 1) = w i * Real.sqrt (f i) from by rw [mul_one],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * Real.sqrt (f i) ^ 2 = w i * f i from by rw [Real.sq_sqrt (hf i)],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show w i * (1 : ℝ) ^ 2 = w i from by ring,
    hw1, Real.sqrt_one, mul_one] at h
  exact h
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_mul_bOp_eq (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    (aOp U : Matrix (dA × dB) _ ℂ) * bOp V = U ⊗ₖ V := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem bornProb_eq_qform (ψ : dA × dB → ℂ) (U : Matrix dA dA ℂ) (V : Matrix dB dB ℂ) :
    bornProb ψ U V = qform ψ ((aOp U : Matrix (dA × dB) _ ℂ) * bOp V) := by
  rw [aOp_mul_bOp_eq, bornProb, qform]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem stateSqNorm_eq_qform (ψ : dA × dB → ℂ) (M : Matrix dA dA ℂ) :
    stateSqNorm ψ M = qform ψ ((aOp (Mᴴ * M) : Matrix (dA × dB) _ ℂ)) := by
  rw [stateSqNorm, stateNorm, norm_stateVec_eq_snorm, snorm_sq_eq_qform, aOp_conjTranspose,
    ← aOp_mul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {X Z : A → Matrix dA dA ℂ} {X' Z' : A → Matrix dB dB ℂ}
/-- The ordered products' squared norms sum to exactly one. -/
theorem sum_stateSqNorm_ord (hψ : ‖evec ψ‖ = 1) (hX : IsPVM X) (hZ : IsPVM Z) :
    ∑ p : A × A, stateSqNorm ψ (X p.1 * Z p.2) = (1 : ℝ) := by
  classical
  have hterm : ∀ p : A × A, stateSqNorm ψ (X p.1 * Z p.2)
      = qform ψ ((aOp (sand X Z p) : Matrix (dA × dB) _ ℂ)) := by
    intro p
    rw [stateSqNorm_eq_qform (dB := dB) ψ, ← sand_eq_gram hX hZ]
  rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hterm p, ← qform_sum, ← aOp_sum,
    sum_sand hX hZ, aOp_one, qform_one _ hψ]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {X Z : A → Matrix dA dA ℂ} {X' Z' : A → Matrix dB dB ℂ}
/-- **Link 4**: Bob's `X`-outcome sums away, exactly. -/
theorem link4_eq (hX' : IsPVM X') :
    ∑ p : A × A, qform ψ ((aOp (Z p.2) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1))
      = ∑ b : A, qform ψ ((aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b)) := by
  classical
  rw [sum_prod_swap (fun p : A × A => qform ψ
    ((aOp (Z p.2) : Matrix (dA × dB) _ ℂ) * bOp (Z' p.2 * X' p.1)))]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← qform_sum]
  congr 1
  show (∑ a : A, (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b * X' a))
    = (aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b)
  rw [← Matrix.mul_sum, ← bOp_sum, ← Matrix.mul_sum, hX'.sum_eq_one, Matrix.mul_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {ψ : dA × dB → ℂ} {X Z : A → Matrix dA dA ℂ} {X' Z' : A → Matrix dB dB ℂ}
/-- **Link 5**: the `Z`-agreement is one minus half the `Z`-consistency defect. -/
theorem link5_eq (hψ : ‖evec ψ‖ = 1) (hZ : IsPVM Z) (hZ' : IsPVM Z') :
    ∑ b : A, qform ψ ((aOp (Z b) : Matrix (dA × dB) _ ℂ) * bOp (Z' b))
      = 1 - (∑ b : A, xSqNorm ψ (Z b) (Z' b)) / 2 := by
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => (bornProb_eq_qform ψ (Z b) (Z' b)).symm,
    ← one_sub_sum_bornProb_eq hψ hZ hZ']
  ring
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem norm_evec_eq_one_of_unit {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec ψ‖ = 1 := by
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem _root_.solution {ι : Type*} [Fintype ι] {w : ι → ℝ}
    (hw0 : ∀ i, 0 ≤ w i) (hw1 : ∑ i, w i = 1)
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1)
    {X Z : ι → A → Matrix dA dA ℂ} {X' Z' : ι → A → Matrix dB dB ℂ}
    (hX : ∀ i, IsPVM (X i)) (hZ : ∀ i, IsPVM (Z i))
    (hX' : ∀ i, IsPVM (X' i)) (hZ' : ∀ i, IsPVM (Z' i))
    {cA cB α β : ℝ}
    (hcA : ∑ i, w i * ∑ p : A × A,
        stateSqNorm ψ (X i p.1 * Z i p.2 - Z i p.2 * X i p.1) ≤ cA)
    (hcB : ∑ i, w i * ∑ p : A × A,
        ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 ≤ cB)
    (hα : ∑ i, w i * ∑ a : A, xSqNorm ψ (X i a) (X' i a) ≤ α)
    (hβ : ∑ i, w i * ∑ b : A, xSqNorm ψ (Z i b) (Z' i b) ≤ β) :
    1 - ∑ i, w i * ∑ p : A × A,
          bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)
      ≤ Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2 := by
  classical
  have hψ' : ‖evec ψ‖ = 1 := norm_evec_eq_one_of_unit hψ
  set cAi : ι → ℝ := fun i => ∑ p : A × A,
    stateSqNorm ψ (X i p.1 * Z i p.2 - Z i p.2 * X i p.1) with hcAi
  set cBi : ι → ℝ := fun i => ∑ p : A × A,
    ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 with hcBi
  set αi : ι → ℝ := fun i => ∑ a : A, xSqNorm ψ (X i a) (X' i a) with hαi
  set βi : ι → ℝ := fun i => ∑ b : A, xSqNorm ψ (Z i b) (Z' i b) with hβi
  have hcAi0 : ∀ i, 0 ≤ cAi i := fun i =>
    Finset.sum_nonneg fun p _ => stateSqNorm_nonneg _ _
  have hcBi0 : ∀ i, 0 ≤ cBi i := fun i => Finset.sum_nonneg fun p _ => sq_nonneg _
  have hαi0 : ∀ i, 0 ≤ αi i := fun i => Finset.sum_nonneg fun a _ => xSqNorm_nonneg _ _ _
  -- the pointwise chain
  have hpt : ∀ i, 1 - ∑ p : A × A,
        bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)
      ≤ Real.sqrt (cAi i) + Real.sqrt (cBi i) + Real.sqrt (αi i / 2) + βi i / 2 := by
    intro i
    have hborn : ∀ p : A × A,
        bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)
          = qform ψ ((aOp (sand (X i) (Z i) p) : Matrix (dA × dB) _ ℂ)
              * bOp (sand (X' i) (Z' i) p)) := fun p => bornProb_eq_qform ψ _ _
    rw [Finset.sum_congr rfl fun p (_ : p ∈ univ) => hborn p]
    -- the four links
    have h1 := abs_link1_le (ψ := ψ) (X := X i) (hZ i) (S' := sand (X' i) (Z' i))
      fun p => sand_conjTranspose (hX' i) (hZ' i) p
    have h2 := abs_link2_le (X := X i) (Z := Z i) (X' := X' i) (Z' := Z' i)
      (ψ := ψ) (hX i) (hZ i) (hZ' i)
    have h3 := abs_link3_le (ψ := ψ) hψ' (hX i) (hZ i) (hX' i) (hZ' i)
    have h4 := link4_eq (ψ := ψ) (Z := Z i) (Z' := Z' i) (hX' i)
    have h5 := link5_eq (ψ := ψ) hψ' (hZ i) (hZ' i)
    -- the two normalizations
    have hB1 : ∑ p : A × A, ‖stateVecB ψ (sand (X' i) (Z' i) p)‖ ^ 2 ≤ 1 := by
      have h := sum_stateSqNormB_le_one (dA := dA) (B := A × A) hψ (sandPOVM (hX' i) (hZ' i))
      simpa using h
    have hA1 : ∑ p : A × A, stateSqNorm ψ (X i p.1 * Z i p.2) = 1 :=
      sum_stateSqNorm_ord (dB := dB) hψ' (hX i) (hZ i)
    -- link 1's second factor and link 2's first factor are at most one
    have hs1 : Real.sqrt (∑ p : A × A, ‖stateVecB ψ (sand (X' i) (Z' i) p)‖ ^ 2) ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hB1
    have hs2 : Real.sqrt (∑ p : A × A, stateSqNorm ψ (X i p.1 * Z i p.2)) = 1 := by
      rw [hA1, Real.sqrt_one]
    have hsA0 : 0 ≤ Real.sqrt (cAi i) := Real.sqrt_nonneg _
    have hsB0 : 0 ≤ Real.sqrt (cBi i) := Real.sqrt_nonneg _
    have h1' : |(∑ p : A × A, qform ψ ((aOp (sand (X i) (Z i) p) : Matrix (dA × dB) _ ℂ)
          * bOp (sand (X' i) (Z' i) p)))
        - ∑ p : A × A, qform ψ ((aOp (Z i p.2 * X i p.1) : Matrix (dA × dB) _ ℂ)
          * bOp (sand (X' i) (Z' i) p))| ≤ Real.sqrt (cAi i) := by
      refine le_trans h1 ?_
      calc Real.sqrt (cAi i)
            * Real.sqrt (∑ p : A × A, ‖stateVecB ψ (sand (X' i) (Z' i) p)‖ ^ 2)
          ≤ Real.sqrt (cAi i) * 1 := mul_le_mul_of_nonneg_left hs1 hsA0
        _ = Real.sqrt (cAi i) := mul_one _
    have h2' : |(∑ p : A × A, qform ψ ((aOp (Z i p.2 * X i p.1) : Matrix (dA × dB) _ ℂ)
          * bOp (sand (X' i) (Z' i) p)))
        - ∑ p : A × A, qform ψ ((aOp (Z i p.2 * X i p.1) : Matrix (dA × dB) _ ℂ)
          * bOp (Z' i p.2 * X' i p.1))| ≤ Real.sqrt (cBi i) := by
      refine le_trans h2 ?_
      rw [hs2, one_mul]
    have habs1 := abs_le.mp h1'
    have habs2 := abs_le.mp h2'
    have habs3 := abs_le.mp h3
    rw [h4, h5] at habs3
    linarith [habs1.1, habs1.2, habs2.1, habs2.2, habs3.1, habs3.2]
  -- average
  have hsum : 1 - ∑ i, w i * ∑ p : A × A,
        bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)
      = ∑ i, w i * (1 - ∑ p : A × A,
          bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)) := by
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_sub (w i) 1 _, Finset.sum_sub_distrib,
      Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_one (w i), hw1]
  rw [hsum]
  refine le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hw0 i)) ?_
  have hsplit : ∑ i, w i * (Real.sqrt (cAi i) + Real.sqrt (cBi i)
        + Real.sqrt (αi i / 2) + βi i / 2)
      = (∑ i, w i * Real.sqrt (cAi i)) + (∑ i, w i * Real.sqrt (cBi i))
        + (∑ i, w i * Real.sqrt (αi i / 2)) + ∑ i, w i * (βi i / 2) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsplit]
  have jA : ∑ i, w i * Real.sqrt (cAi i) ≤ Real.sqrt cA :=
    le_trans (sum_weighted_sqrt_le w cAi hw0 hw1 hcAi0) (Real.sqrt_le_sqrt hcA)
  have jB : ∑ i, w i * Real.sqrt (cBi i) ≤ Real.sqrt cB :=
    le_trans (sum_weighted_sqrt_le w cBi hw0 hw1 hcBi0) (Real.sqrt_le_sqrt hcB)
  have jα : ∑ i, w i * Real.sqrt (αi i / 2) ≤ Real.sqrt (α / 2) := by
    refine le_trans (sum_weighted_sqrt_le w (fun i => αi i / 2) hw0 hw1
      fun i => by linarith [hαi0 i]) (Real.sqrt_le_sqrt ?_)
    rw [show (∑ i, w i * (αi i / 2)) = (∑ i, w i * αi i) / 2 from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring]
    linarith
  have jβ : ∑ i, w i * (βi i / 2) ≤ β / 2 := by
    rw [show (∑ i, w i * (βi i / 2)) = (∑ i, w i * βi i) / 2 from by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring]
    linarith
  linarith
end MIPRE
