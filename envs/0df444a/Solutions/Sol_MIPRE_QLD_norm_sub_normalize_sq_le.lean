-- Prove2me | solution 1 for MIPRE.QLD.norm_sub_normalize_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T02:45:06.508043+00:00
-- url     : https://prove2.me/submissions/8fc62550-f4ee-4dfb-a288-6fd4a030382d

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/SwapUnitary.lean (solution of MIPRE.QLD.norm_sub_normalize_sq_le);
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
theorem _root_.solution {θ x : E} {η : ℝ} (hθ : ‖θ‖ = 1)
    (hx : ‖x‖ ^ 2 = (inner ℂ θ x : ℂ).re) (hlt : η < 1)
    (hlow : 1 - η ≤ (inner ℂ θ x : ℂ).re) :
    ‖θ - ((‖x‖⁻¹ : ℝ) : ℂ) • x‖ ^ 2 ≤ 2 - 2 * Real.sqrt (1 - η) := by
  have h0 : (0 : ℝ) < 1 - η := by linarith
  have hxpos : 0 < ‖x‖ := by
    rcases eq_or_lt_of_le (norm_nonneg x) with h | h
    · exfalso
      rw [← h] at hx
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at hx
      linarith [hx ▸ hlow]
    · exact h
  -- the norm of the projection is the square root of the weight
  have hnormx : Real.sqrt (1 - η) ≤ ‖x‖ := by
    rw [show ‖x‖ = Real.sqrt (‖x‖ ^ 2) from (Real.sqrt_sq (norm_nonneg _)).symm, hx]
    exact Real.sqrt_le_sqrt hlow
  -- the normalized vector is a unit vector whose overlap with `theta` is that norm
  have hunit : ‖((‖x‖⁻¹ : ℝ) : ℂ) • x‖ = 1 := by
    rw [norm_smul, Complex.norm_real, norm_inv, norm_norm, inv_mul_cancel₀ hxpos.ne']
  have hov : (inner ℂ θ (((‖x‖⁻¹ : ℝ) : ℂ) • x) : ℂ).re = ‖x‖ := by
    rw [inner_smul_right, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero, ← hx]
    field_simp
  rw [norm_sub_sq (𝕜 := ℂ), hθ, hunit]
  simp only [RCLike.re_to_complex]
  rw [hov]
  linarith
end MIPRE.QLD
