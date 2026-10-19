-- Prove2me | solution 1 for MIPRE.QLD.re_inner_ge_of_two_close
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:44:56.691817+00:00
-- url     : https://prove2.me/submissions/d3ff5fe2-4ad8-469b-9355-e27177077fd6

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapUnitary.lean (solution of MIPRE.QLD.re_inner_ge_of_two_close);
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Background_QLD_ExactPauli
import Definitions.Def_MIPRE_Background_QLD_SwapUnitary

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD
open Finset Matrix MIPRE MIPRE.Weyl
open scoped Kronecker ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {dA : Type*} [Fintype dA] [DecidableEq dA]
variable {S : G × G → Matrix dA dA ℂ} {cd : G → (n → F)}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
theorem _root_.solution {θ x y : E} {δ : ℝ} (hδ : 0 ≤ δ) (hθ : ‖θ‖ = 1)
    (hx : ‖θ - x‖ ^ 2 ≤ δ) (hy : ‖θ - y‖ ^ 2 ≤ δ) :
    1 - 2 * Real.sqrt δ - 2 * δ ≤ (inner ℂ x y : ℂ).re := by
  have hs : Real.sqrt δ * Real.sqrt δ = δ := Real.mul_self_sqrt hδ
  have hs0 : (0 : ℝ) ≤ Real.sqrt δ := Real.sqrt_nonneg δ
  have hxd : ‖θ - x‖ ≤ Real.sqrt δ := by
    rw [show ‖θ - x‖ = Real.sqrt (‖θ - x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hx
  have hyd : ‖θ - y‖ ≤ Real.sqrt δ := by
    rw [show ‖θ - y‖ = Real.sqrt (‖θ - y‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm]
    exact Real.sqrt_le_sqrt hy
  -- the triangle inequality on the difference of the two vectors
  have hxy : ‖x - y‖ ≤ 2 * Real.sqrt δ := by
    calc ‖x - y‖ = ‖(θ - y) - (θ - x)‖ := by rw [show (θ - y) - (θ - x) = x - y from by abel]
      _ ≤ ‖θ - y‖ + ‖θ - x‖ := norm_sub_le _ _
      _ ≤ 2 * Real.sqrt δ := by linarith
  have hexp : ‖x - y‖ ^ 2 = ‖x‖ ^ 2 - 2 * (inner ℂ x y : ℂ).re + ‖y‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    simp only [RCLike.re_to_complex]
  have hxy2 : ‖x‖ ^ 2 - 2 * (inner ℂ x y : ℂ).re + ‖y‖ ^ 2 ≤ 4 * δ := by
    rw [← hexp]
    nlinarith [norm_nonneg (x - y)]
  rcases le_or_gt δ 1 with hle | hgt
  · -- the squaring is valid, and gives the stated bound
    have hsle : Real.sqrt δ ≤ 1 := by
      rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hle
    have hxn : 1 - Real.sqrt δ ≤ ‖x‖ := by
      have := norm_sub_norm_le θ x
      rw [hθ] at this
      linarith
    have hyn : 1 - Real.sqrt δ ≤ ‖y‖ := by
      have := norm_sub_norm_le θ y
      rw [hθ] at this
      linarith
    nlinarith
  · -- outside that range the trivial bound is already stronger
    nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖y‖]
end MIPRE.QLD
