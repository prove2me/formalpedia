-- Prove2me | solution 1 for MIPRE.sum_snorm_sq_ge_of_close
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:46:39.633895+00:00
-- url     : https://prove2.me/submissions/e44e6ea9-80c2-42ff-a39f-98d0329c61fc

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (solution of MIPRE.sum_snorm_sq_ge_of_close);
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
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
omit [Fintype N] in
theorem evec_sub (v w : N → ℂ) : evec (v - w) = evec v - evec w := rfl
end
end MIPRE

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
theorem snorm_sub_le (M M' : Matrix N N ℂ) : snorm v (M - M') ≤ snorm v M + snorm v M' := by
  rw [snorm, snorm, snorm, Matrix.sub_mulVec, evec_sub]
  exact norm_sub_le _ _
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

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N] {ι : Type*} [Fintype ι]
theorem _root_.solution (v : N → ℂ) (R O : ι → Matrix N N ℂ)
    (hR : ∑ i, snorm v (R i) ^ 2 ≤ 1) (hO : ∑ i, snorm v (O i) ^ 2 ≤ 1) (acc : Finset ι) :
    ∑ i ∈ acc, snorm v (O i) ^ 2 - 2 * √(∑ i, snorm v (R i - O i) ^ 2)
      ≤ ∑ i ∈ acc, snorm v (R i) ^ 2 := by
  set D : ι → ℝ := fun i => snorm v (R i - O i) with hD
  set s : ι → ℝ := fun i => snorm v (O i) + snorm v (R i) with hs
  have hterm : ∀ i, snorm v (O i) ^ 2 - snorm v (R i) ^ 2 ≤ D i * s i := by
    intro i
    have h1 : snorm v (O i) ≤ snorm v (R i) + D i := by
      have h := snorm_sub_le v (R i) (R i - O i)
      rwa [sub_sub_cancel] at h
    have h0 := snorm_nonneg v (O i)
    have h0' := snorm_nonneg v (R i)
    have hk : 0 ≤ (D i - (snorm v (O i) - snorm v (R i))) * s i :=
      mul_nonneg (by linarith) (by simp only [hs]; linarith)
    simp only [hs] at hk ⊢
    nlinarith [hk]
  have hD0 : ∀ i, 0 ≤ D i * s i := fun i =>
    mul_nonneg (snorm_nonneg v _) (add_nonneg (snorm_nonneg v _) (snorm_nonneg v _))
  have hsum : ∑ i ∈ acc, snorm v (O i) ^ 2 - ∑ i ∈ acc, snorm v (R i) ^ 2
      ≤ ∑ i, D i * s i := by
    rw [← Finset.sum_sub_distrib]
    calc ∑ i ∈ acc, (snorm v (O i) ^ 2 - snorm v (R i) ^ 2) ≤ ∑ i ∈ acc, D i * s i :=
          Finset.sum_le_sum fun i _ => hterm i
      _ ≤ ∑ i, D i * s i :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ => hD0 i
  have hs2 : ∑ i, s i ^ 2 ≤ 4 := by
    have hle : ∀ i, s i ^ 2 ≤ 2 * snorm v (O i) ^ 2 + 2 * snorm v (R i) ^ 2 := fun i => by
      simp only [hs]
      nlinarith [sq_nonneg (snorm v (O i) - snorm v (R i))]
    calc ∑ i, s i ^ 2 ≤ ∑ i, (2 * snorm v (O i) ^ 2 + 2 * snorm v (R i) ^ 2) :=
          Finset.sum_le_sum fun i _ => hle i
      _ = 2 * ∑ i, snorm v (O i) ^ 2 + 2 * ∑ i, snorm v (R i) ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 4 := by linarith
  have hsq : √(∑ i, s i ^ 2) ≤ 2 := by
    rw [show (2 : ℝ) = √4 by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]]
    exact Real.sqrt_le_sqrt hs2
  have hcs : ∑ i, D i * s i ≤ 2 * √(∑ i, D i ^ 2) :=
    calc ∑ i, D i * s i ≤ √(∑ i, D i ^ 2) * √(∑ i, s i ^ 2) := sum_mul_le_sqrt D s
      _ ≤ √(∑ i, D i ^ 2) * 2 := mul_le_mul_of_nonneg_left hsq (Real.sqrt_nonneg _)
      _ = 2 * √(∑ i, D i ^ 2) := by ring
  have hDsq : ∑ i, D i ^ 2 = ∑ i, snorm v (R i - O i) ^ 2 := rfl
  rw [hDsq] at hcs
  linarith
end MIPRE
