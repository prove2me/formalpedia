-- Prove2me | solution 1 for MIPRE.sum_weighted_mul_le_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:45:45.694005+00:00
-- url     : https://prove2.me/submissions/071c2f5e-711c-45bc-82c9-6a765ada9fe1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sandwich.lean (solution of MIPRE.sum_weighted_mul_le_sqrt);
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
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
theorem _root_.solution {ι : Type*} [Fintype ι] (w u v : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    ∑ i, w i * (u i * v i)
      ≤ Real.sqrt (∑ i, w i * u i ^ 2) * Real.sqrt (∑ i, w i * v i ^ 2) := by
  classical
  set f : ι → ℝ := fun i => Real.sqrt (w i) * u i with hf
  set g : ι → ℝ := fun i => Real.sqrt (w i) * v i with hg
  have hfg : ∀ i, f i * g i = w i * (u i * v i) := by
    intro i
    rw [hf, hg]
    show Real.sqrt (w i) * u i * (Real.sqrt (w i) * v i) = w i * (u i * v i)
    rw [show Real.sqrt (w i) * u i * (Real.sqrt (w i) * v i)
        = (Real.sqrt (w i) * Real.sqrt (w i)) * (u i * v i) from by ring,
      Real.mul_self_sqrt (hw i)]
  have hf2 : ∀ i, f i ^ 2 = w i * u i ^ 2 := by
    intro i
    rw [hf]
    show (Real.sqrt (w i) * u i) ^ 2 = w i * u i ^ 2
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hg2 : ∀ i, g i ^ 2 = w i * v i ^ 2 := by
    intro i
    rw [hg]
    show (Real.sqrt (w i) * v i) ^ 2 = w i * v i ^ 2
    rw [mul_pow, Real.sq_sqrt (hw i)]
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq (univ : Finset ι) f g
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => hf2 i,
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => hg2 i] at hCS
  have hnn : 0 ≤ ∑ i, w i * u i ^ 2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i) (sq_nonneg _)
  calc ∑ i, w i * (u i * v i) = ∑ i, f i * g i :=
        (Finset.sum_congr rfl fun i _ => hfg i).symm
    _ ≤ |∑ i, f i * g i| := le_abs_self _
    _ = Real.sqrt ((∑ i, f i * g i) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((∑ i, w i * u i ^ 2) * ∑ i, w i * v i ^ 2) := Real.sqrt_le_sqrt hCS
    _ = Real.sqrt (∑ i, w i * u i ^ 2) * Real.sqrt (∑ i, w i * v i ^ 2) := Real.sqrt_mul hnn _
end MIPRE
