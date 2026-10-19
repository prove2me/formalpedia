-- Prove2me | solution 1 for MIPRE.Introspection.submeasurement_completion_dist_avg
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:31:40.166987+00:00
-- url     : https://prove2.me/submissions/aa45a7ea-05fb-42c0-9034-ecb550f76316

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/SubmeasurementCompletion.lean (solution of MIPRE.Introspection.submeasurement_completion_dist_avg);
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
import Theorems.Thm_MIPRE_Introspection_submeasurement_completion_mass
import Theorems.Thm_MIPRE_qform_sum_ge_of_close
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_nonneg (M : Matrix N N ℂ) : 0 ≤ snorm v M := norm_nonneg _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_add_le (M M' : Matrix N N ℂ) : snorm v (M + M') ≤ snorm v M + snorm v M' := by
  rw [snorm, snorm, snorm, Matrix.add_mulVec, evec_add]
  exact norm_add_le _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
/-- The triangle inequality for a family of deviations, at the usual cost of a factor two. -/
theorem sum_snorm_sq_triangle' {ι : Type*} [Fintype ι] (v : N → ℂ)
    (P Q R : ι → Matrix N N ℂ) :
    ∑ i, snorm v (P i - R i) ^ 2
      ≤ 2 * ∑ i, snorm v (P i - Q i) ^ 2 + 2 * ∑ i, snorm v (Q i - R i) ^ 2 := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hsplit : P i - R i = (P i - Q i) + (Q i - R i) := by abel
  have htri : snorm v (P i - R i) ≤ snorm v (P i - Q i) + snorm v (Q i - R i) := by
    rw [hsplit]; exact snorm_add_le v _ _
  nlinarith [snorm_nonneg v (P i - Q i), snorm_nonneg v (Q i - R i),
    snorm_nonneg v (P i - R i), sq_nonneg (snorm v (P i - Q i) - snorm v (Q i - R i))]
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

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A] [DecidableEq A]
/-- A POVM completing a nearby submeasurement stays close to the original PVM. -/
theorem submeasurement_completion_dist (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P B C : A → Matrix N N ℂ) (hP : IsPVM P)
    (hB : ∀ a, 0 ≤ B a) (hC : ∀ a, 0 ≤ C a)
    (hCsum : ∑ a, C a = 1) (hBC : ∀ a, B a ≤ C a)
    {δ : ℝ} (hclose : ∑ a, snorm ψ (P a - B a) ^ 2 ≤ δ) :
    (∑ a, snorm ψ (P a - C a) ^ 2) ≤ 2 * δ + 4 * Real.sqrt δ := by
  have hBsum : ∑ a, B a ≤ (1 : Matrix N N ℂ) :=
    (Finset.sum_le_sum fun a _ => hBC a).trans_eq hCsum
  have hmass := qform_sum_ge_of_close hψ hP hB hBsum hclose
  have hfill := submeasurement_completion_mass ψ hψ B C hB hC hCsum hBC
  have htri := sum_snorm_sq_triangle' ψ P B C
  linarith
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N A : Type*} [Fintype N] [DecidableEq N] [Fintype A] [DecidableEq A]
theorem _root_.solution {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (ψ : N → ℂ) (hψ : ‖evec ψ‖ = 1)
    (P B C : X → A → Matrix N N ℂ) (hP : ∀ x, IsPVM (P x))
    (hB : ∀ x a, 0 ≤ B x a) (hC : ∀ x a, 0 ≤ C x a)
    (hCsum : ∀ x, ∑ a, C x a = 1) (hBC : ∀ x a, B x a ≤ C x a)
    {δ : ℝ} (hclose : ∑ x, D x * ∑ a, snorm ψ (P x a - B x a) ^ 2 ≤ δ) :
    (∑ x, D x * ∑ a, snorm ψ (P x a - C x a) ^ 2) ≤
      2 * δ + 4 * Real.sqrt δ := by
  let E x := ∑ a, snorm ψ (P x a - B x a) ^ 2
  have hE0 x : 0 ≤ E x := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hpoint x := submeasurement_completion_dist ψ hψ (P x) (B x) (C x)
    (hP x) (hB x) (hC x) (hCsum x) (hBC x) (le_refl (E x))
  have hsum := Finset.sum_le_sum (fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left (hpoint x) (hD0 x))
  have hroot := (sum_weighted_sqrt_le D E hD0 hD1 hE0).trans (Real.sqrt_le_sqrt hclose)
  have heq : (∑ x, D x * (2 * E x + 4 * Real.sqrt (E x))) =
      2 * (∑ x, D x * E x) + 4 * ∑ x, D x * Real.sqrt (E x) := by
    simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
  change _ ≤ ∑ x, D x * (2 * E x + 4 * Real.sqrt (E x)) at hsum
  rw [heq] at hsum
  linarith
end MIPRE.Introspection
