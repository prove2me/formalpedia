-- Prove2me | solution 1 for MIPRE.commutation_analysis_abstract
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:42:30.757563+00:00
-- url     : https://prove2.me/submissions/071e8038-9687-43f8-b89b-91841d718044

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Commutation.lean (solution of MIPRE.commutation_analysis_abstract);
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
import Theorems.Thm_MIPRE_sum_snorm_sq_mul_le

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
theorem snorm_add_le (M M' : Matrix N N ℂ) : snorm v (M + M') ≤ snorm v M + snorm v M' := by
  rw [snorm, snorm, snorm, Matrix.add_mulVec, evec_add]
  exact norm_add_le _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
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
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N] {B C : Type*} [Fintype B] [Fintype C]
  {v : N → ℂ} {δ : ℝ}
/-- Putting a family in front, with the front index in the first component of the pair. -/
theorem sum_prod_snorm_sq_mul_le_fst (v : N → ℂ)
    (F : B → Matrix N N ℂ) (hF : ∑ b, (F b)ᴴ * F b ≤ (1 : Matrix N N ℂ))
    (M : C → Matrix N N ℂ) :
    ∑ p : B × C, snorm v (F p.1 * M p.2) ^ 2 ≤ ∑ c, snorm v (M c) ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  exact Finset.sum_le_sum fun c _ => sum_snorm_sq_mul_le v F hF (M c)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N] {B C : Type*} [Fintype B] [Fintype C]
  {v : N → ℂ} {δ : ℝ}
/-- Putting a family in front, with the front index in the second component. -/
theorem sum_prod_snorm_sq_mul_le_snd (v : N → ℂ)
    (F : C → Matrix N N ℂ) (hF : ∑ c, (F c)ᴴ * F c ≤ (1 : Matrix N N ℂ))
    (M : B → Matrix N N ℂ) :
    ∑ p : B × C, snorm v (F p.2 * M p.1) ^ 2 ≤ ∑ b, snorm v (M b) ^ 2 := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_le_sum fun b _ => sum_snorm_sq_mul_le v F hF (M b)
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N] [DecidableEq N] {B C : Type*} [Fintype B] [Fintype C]
  {v : N → ℂ} {δ : ℝ}
theorem _root_.solution (v : N → ℂ)
    (alpha : B → Matrix N N ℂ) (gamma : C → Matrix N N ℂ)
    (betaB : B → Matrix N N ℂ) (betaC : C → Matrix N N ℂ)
    (betaBC : B × C → Matrix N N ℂ)
    (halpha : ∑ b, (alpha b)ᴴ * alpha b ≤ (1 : Matrix N N ℂ))
    (hgamma : ∑ c, (gamma c)ᴴ * gamma c ≤ (1 : Matrix N N ℂ))
    (hbetaB : ∑ b, (betaB b)ᴴ * betaB b ≤ (1 : Matrix N N ℂ))
    (hbetaC : ∑ c, (betaC c)ᴴ * betaC c ≤ (1 : Matrix N N ℂ))
    (hcomm : ∀ b c, alpha b * betaC c = betaC c * alpha b)
    (hcomm' : ∀ b c, gamma c * betaB b = betaB b * gamma c)
    (hmul : ∀ b c, betaC c * betaB b = betaBC (b, c))
    (hmul' : ∀ b c, betaB b * betaC c = betaBC (b, c))
    (hA : ∑ b, snorm v (alpha b - betaB b) ^ 2 ≤ δ)
    (hC : ∑ c, snorm v (gamma c - betaC c) ^ 2 ≤ δ) :
    ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - gamma p.2 * alpha p.1) ^ 2 ≤ 16 * δ := by
  classical
  -- `alpha_b gamma_c` reaches `betaBC` in two steps
  have s1 : ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - alpha p.1 * betaC p.2) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (sum_prod_snorm_sq_mul_le_fst v alpha halpha
        (fun c => gamma c - betaC c)) hC)
    rw [Matrix.mul_sub]
  have s2 : ∑ p : B × C, snorm v (alpha p.1 * betaC p.2 - betaBC p) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (sum_prod_snorm_sq_mul_le_snd v betaC hbetaC
        (fun b => alpha b - betaB b)) hA)
    rw [Matrix.mul_sub, ← hcomm p.1 p.2, hmul p.1 p.2]
  have h1 : ∑ p : B × C, snorm v (alpha p.1 * gamma p.2 - betaBC p) ^ 2 ≤ 4 * δ := by
    refine le_trans (sum_snorm_sq_triangle' v _ (fun p => alpha p.1 * betaC p.2) _) ?_
    linarith
  -- `gamma_c alpha_b` reaches the same operator
  have s3 : ∑ p : B × C, snorm v (gamma p.2 * alpha p.1 - gamma p.2 * betaB p.1) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (sum_prod_snorm_sq_mul_le_snd v gamma hgamma
        (fun b => alpha b - betaB b)) hA)
    rw [Matrix.mul_sub]
  have s4 : ∑ p : B × C, snorm v (gamma p.2 * betaB p.1 - betaBC p) ^ 2 ≤ δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_))
      (le_trans (sum_prod_snorm_sq_mul_le_fst v betaB hbetaB
        (fun c => gamma c - betaC c)) hC)
    rw [Matrix.mul_sub, ← hcomm' p.1 p.2, hmul' p.1 p.2]
  have h2 : ∑ p : B × C, snorm v (gamma p.2 * alpha p.1 - betaBC p) ^ 2 ≤ 4 * δ := by
    refine le_trans (sum_snorm_sq_triangle' v _ (fun p => gamma p.2 * betaB p.1) _) ?_
    linarith
  have h2' : ∑ p : B × C, snorm v (betaBC p - gamma p.2 * alpha p.1) ^ 2 ≤ 4 * δ := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) h2
    rw [snorm_sub_comm]
  refine le_trans (sum_snorm_sq_triangle' v _ betaBC _) ?_
  linarith
end MIPRE
