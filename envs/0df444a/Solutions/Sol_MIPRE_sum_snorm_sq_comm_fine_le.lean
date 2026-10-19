-- Prove2me | solution 1 for MIPRE.sum_snorm_sq_comm_fine_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:35:51.023654+00:00
-- url     : https://prove2.me/submissions/eabbd3dc-f5b2-4fbf-9fce-94960f565f27

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Pasting.lean (solution of MIPRE.sum_snorm_sq_comm_fine_le);
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
import Theorems.Thm_MIPRE_IsPVM_coarse
import Theorems.Thm_MIPRE_abs_sigma_sub_cloud_le
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_eq
import Theorems.Thm_MIPRE_strife_sub_cloud_eq
import Theorems.Thm_MIPRE_sum_bornProb_le_fibSum
import Theorems.Thm_MIPRE_sum_snorm_sq_comm_coarse_le
import Theorems.Thm_MIPRE_sum_snorm_sq_comm_eq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
theorem isPVM_fibSum {G : α → Matrix N N ℂ} (h : IsPVM G) (e : α → β) : IsPVM (fibSum G e) :=
  h.coarse e
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
  {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
/-- **Coarse-graining two projective families the same way costs nothing**, in the `fibSum` form
that the pasting lemma needs. -/
theorem sum_xSqNorm_fibSum_le {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1) {X : α → Matrix dA dA ℂ}
    {X' : α → Matrix dB dB ℂ} (hX : IsPVM X) (hX' : IsPVM X') (e : α → β) :
    ∑ b, xSqNorm ψ (fibSum X e b) (fibSum X' e b) ≤ ∑ a, xSqNorm ψ (X a) (X' a) := by
  have e1 := one_sub_sum_bornProb_eq hψ (isPVM_fibSum hX e) (isPVM_fibSum hX' e)
  have e2 := one_sub_sum_bornProb_eq hψ hX hX'
  have e3 := sum_bornProb_le_fibSum ψ hX hX' e
  linarith
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 K : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
  [Fintype K] [DecidableEq K]
variable {R : R1 → Matrix dB dB ℂ} {G : K → Matrix dB dB ℂ}
theorem _root_.solution {ψ : dA × dB → ℂ} (hψ : ‖evec ψ‖ = 1)
    {A : R1 × R2 → Matrix dA dA ℂ} {Ga : K → Matrix dA dA ℂ} (hA : IsPVM A) (hR : IsPVM R)
    (hG : IsPVM G) (hGa : IsPVM Ga) (e : K → R2) {δ₁ δ₂ : ℝ}
    (h1 : ∑ a : R1, xSqNorm ψ (∑ b : R2, A (a, b)) (R a) ≤ δ₁)
    (h2 : ∑ b : R2, xSqNorm ψ (∑ a : R1, A (a, b)) (fibSum G e b) ≤ δ₂) :
    (∑ a : R1, ∑ g : K, snorm ψ (bOp (R a * G g - G g * R a) : Matrix (dA × dB) _ ℂ) ^ 2)
      ≤ 16 * (δ₁ + δ₂) + 4 * Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g))
        + 2 * collisionTerm ψ R G Ga e := by
  have hfine := sum_snorm_sq_comm_eq (dA := dA) hψ hR hG
  have hcoarse := sum_snorm_sq_comm_eq (dA := dA) hψ hR (isPVM_fibSum hG e)
  have hcc := sum_snorm_sq_comm_coarse_le (ψ := ψ) hA hR (isPVM_fibSum hG e) h1 h2
  have hc1 := abs_le.mp (abs_sigma_sub_cloud_le (Ga := Ga) hψ hR hG)
  have hc2 := abs_le.mp (abs_sigma_sub_cloud_le (K := R2) (G := fibSum G e)
    (Ga := fibSum Ga e) hψ hR (isPVM_fibSum hG e))
  have hcol := strife_sub_cloud_eq (ψ := ψ) (R := R) (G := G) (Ga := Ga) e
  have hmono : Real.sqrt (∑ b : R2, xSqNorm ψ (fibSum Ga e b) (fibSum G e b))
      ≤ Real.sqrt (∑ g : K, xSqNorm ψ (Ga g) (G g)) :=
    Real.sqrt_le_sqrt (sum_xSqNorm_fibSum_le hψ hGa hG e)
  linarith [hc1.1, hc1.2, hc2.1, hc2.2]
end MIPRE
