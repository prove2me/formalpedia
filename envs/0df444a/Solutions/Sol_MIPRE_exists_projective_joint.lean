-- Prove2me | solution 1 for MIPRE.exists_projective_joint
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:36:17.918187+00:00
-- url     : https://prove2.me/submissions/7e410936-2955-4f62-aa23-92cd426b30e1

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Sandwich.lean (solution of MIPRE.exists_projective_joint);
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
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_bnd_one_of_conjTranspose_mul_self_le
import Theorems.Thm_MIPRE_exists_projective_dilation
import Theorems.Thm_MIPRE_normSq_stateVecB_extVec2_aOp
import Theorems.Thm_MIPRE_norm_stateVecB
import Theorems.Thm_MIPRE_one_sub_sum_bornProb_sand_le
import Theorems.Thm_MIPRE_sum_stateSqNorm_le_one
import Theorems.Thm_MIPRE_sum_xSqNorm_dilated_aOp_le
import Theorems.Thm_MIPRE_sum_xSqNorm_dilated_eq
import Theorems.Thm_MIPRE_swapVec_dotProduct

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
/-- A bound in front of anything. -/
theorem snorm_mul_le {M : Matrix N N ℂ} {K : ℝ} (h : Bnd M K) (M' : Matrix N N ℂ) :
    snorm v (M * M') ≤ K * snorm v M' := by
  rw [snorm, snorm, ← Matrix.mulVec_mulVec]
  exact h (M' *ᵥ v)
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
theorem bOp_mul (X Y : Matrix HB HB ℂ) :
    bOp (X * Y) = (bOp X : Matrix (HA × HB) _ ℂ) * bOp Y := by
  rw [bOp, bOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
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
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem bOp_smul (c : ℂ) (X : Matrix HB HB ℂ) :
    bOp (c • X) = c • (bOp X : Matrix (HA × HB) _ ℂ) := Matrix.kronecker_smul _ _ _
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
theorem bOp_sub (X Y : Matrix HB HB ℂ) :
    bOp (X - Y) = (bOp X : Matrix (HA × HB) _ ℂ) - bOp Y := by
  have h : X - Y = X + (-1 : ℂ) • Y := by module
  rw [h, bOp_add, bOp_smul]
  module
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
theorem bOp_conjTranspose (X : Matrix HB HB ℂ) :
    (bOp X : Matrix (HA × HB) _ ℂ)ᴴ = bOp (Xᴴ) := by
  rw [bOp, bOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one]
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
theorem bOp_nonneg {Y : Matrix HB HB ℂ} (hY : (0 : Matrix HB HB ℂ) ≤ Y) :
    (0 : Matrix (HA × HB) (HA × HB) ℂ) ≤ bOp Y :=
  Matrix.nonneg_iff_posSemidef.mpr
    (Matrix.PosSemidef.one.kronecker (Matrix.nonneg_iff_posSemidef.mp hY))
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
/-- A contraction on the second factor is a contraction on the product space. -/
theorem bnd_bOp {Y : Matrix HB HB ℂ} (h : (Yᴴ * Y) ≤ (1 : Matrix HB HB ℂ)) :
    Bnd (bOp Y : Matrix (HA × HB) _ ℂ) 1 := by
  refine bnd_one_of_conjTranspose_mul_self_le ?_
  rw [bOp_conjTranspose, ← bOp_mul, ← bOp_one (HA := HA) (HB := HB)]
  refine sub_nonneg.mp ?_
  rw [← bOp_sub]
  exact bOp_nonneg (sub_nonneg.mpr h)
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
theorem xNorm_nonneg (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    0 ≤ xNorm ψ A B := norm_nonneg _
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
theorem xSqNorm_eq_sq (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xSqNorm ψ A B = xNorm ψ A B ^ 2 := rfl
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
omit [DecidableEq dB] in
theorem norm_stateVecB_eq_snorm (ψ : dA × dB → ℂ) (B : Matrix dB dB ℂ) :
    ‖stateVecB ψ B‖ = snorm ψ (bOp B : Matrix (dA × dB) _ ℂ) := rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- **A projection is bounded by the identity.** -/
theorem proj_le_one {P : Matrix N N ℂ} (hsa : Pᴴ = P) (hidem : P * P = P) :
    P ≤ (1 : Matrix N N ℂ) := by
  refine sub_nonneg.mp (Matrix.nonneg_iff_posSemidef.mpr ?_)
  have h : (1 : Matrix N N ℂ) - P = ((1 : Matrix N N ℂ) - P)ᴴ * ((1 : Matrix N N ℂ) - P) := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hsa, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.one_mul, hidem]
    abel
  rw [h]
  exact Matrix.posSemidef_conjTranspose_mul_self _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **A contraction in front costs nothing**, on Bob's side. -/
theorem norm_stateVecB_mul_le (ψ : dA × dB → ℂ) {P : Matrix dB dB ℂ}
    (hP : Pᴴ * P ≤ (1 : Matrix dB dB ℂ)) (N : Matrix dB dB ℂ) :
    ‖stateVecB ψ (P * N)‖ ≤ ‖stateVecB ψ N‖ := by
  rw [norm_stateVecB_eq_snorm, norm_stateVecB_eq_snorm, bOp_mul]
  have h := snorm_mul_le ψ (bnd_bOp (HA := dA) hP) (bOp N : Matrix (dA × dB) _ ℂ)
  rwa [one_mul] at h
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
/-- A projective measurement's elements are contractions. -/
theorem IsPVM.conjTranspose_mul_self_le_one {N : Type*} [Fintype N] [DecidableEq N]
    {P : A → Matrix N N ℂ} (h : IsPVM P) (a : A) : (P a)ᴴ * P a ≤ (1 : Matrix N N ℂ) := by
  rw [h.isSelfAdjoint a, h.idem a]
  exact proj_le_one (h.isSelfAdjoint a) (h.idem a)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem stateVecB_add' (ψ : dA × dB → ℂ) (M N : Matrix dB dB ℂ) :
    stateVecB ψ (M + N) = stateVecB ψ M + stateVecB ψ N := by
  show WithLp.toLp 2 _ = WithLp.toLp 2 _ + WithLp.toLp 2 _
  rw [Matrix.kronecker_add, Matrix.add_mulVec]
  rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem stateVecB_sub' (ψ : dA × dB → ℂ) (M N : Matrix dB dB ℂ) :
    stateVecB ψ (M - N) = stateVecB ψ M - stateVecB ψ N := by
  have h : M - N = M + (-1 : ℂ) • N := by module
  rw [h, stateVecB_add', stateVecB_smul]
  module
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **Replacing Bob's operator inside a cross-party deviation.** -/
theorem xNorm_le_add_stateVecB (ψ : dA × dB → ℂ) (Aop : Matrix dA dA ℂ) (B₁ B₂ : Matrix dB dB ℂ) :
    xNorm ψ Aop B₂ ≤ xNorm ψ Aop B₁ + ‖stateVecB ψ (B₁ - B₂)‖ := by
  rw [xNorm, xNorm, stateVecB_sub',
    show stateVec ψ Aop - stateVecB ψ B₂
      = (stateVec ψ Aop - stateVecB ψ B₁) + (stateVecB ψ B₁ - stateVecB ψ B₂) from by abel]
  exact norm_add_le _ _
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem norm_stateVecB_extVec2_aOp {Anc Bnc : Type*} [Fintype Anc] [DecidableEq Anc]
    [Fintype Bnc] [DecidableEq Bnc] (ψ : dA × dB → ℂ) (a₀ : Anc) (b₀ : Bnc)
    (N : Matrix dB dB ℂ) :
    ‖stateVecB (extVec2 ψ a₀ b₀) (aOp N : Matrix (dB × Bnc) _ ℂ)‖ = ‖stateVecB ψ N‖ := by
  have h := normSq_stateVecB_extVec2_aOp ψ a₀ b₀ N
  nlinarith [norm_nonneg (stateVecB (extVec2 ψ a₀ b₀) (aOp N : Matrix (dB × Bnc) _ ℂ)),
    norm_nonneg (stateVecB ψ N), h]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {A : Type*} [Fintype A] [DecidableEq A]
  {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- **Replacing Bob's operator inside a squared cross-party deviation**, at the usual factor
two. -/
theorem xSqNorm_le_of_stateVecB (ψ : dA × dB → ℂ) (Aop : Matrix dA dA ℂ)
    (B₁ B₂ : Matrix dB dB ℂ) :
    xSqNorm ψ Aop B₂ ≤ 2 * xSqNorm ψ Aop B₁ + 2 * ‖stateVecB ψ (B₁ - B₂)‖ ^ 2 := by
  have h := xNorm_le_add_stateVecB ψ Aop B₁ B₂
  rw [xSqNorm_eq_sq, xSqNorm_eq_sq]
  nlinarith [xNorm_nonneg ψ Aop B₂, xNorm_nonneg ψ Aop B₁,
    norm_nonneg (stateVecB ψ (B₁ - B₂)),
    sq_nonneg (xNorm ψ Aop B₁ - ‖stateVecB ψ (B₁ - B₂)‖)]
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
    {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) (a₀ : A × A)
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
    ∃ (QA : ι → (A × A) → Matrix (dA × (A × A)) (dA × (A × A)) ℂ)
      (QB : ι → (A × A) → Matrix (dB × (A × A)) (dB × (A × A)) ℂ),
      (∀ i, IsPVM (QA i)) ∧ (∀ i, IsPVM (QB i))
      ∧ (∀ i p, (ancillaEmbed dA a₀)ᴴ * (QA i p * ancillaEmbed dA a₀) = sand (X i) (Z i) p)
      ∧ (∀ i p, (ancillaEmbed dB a₀)ᴴ * (QB i p * ancillaEmbed dB a₀) = sand (X' i) (Z' i) p)
      ∧ (∑ i, w i * ∑ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (QA i p) (QB i p)
          ≤ 2 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2))
      ∧ (∑ i, w i * ∑ p : A × A,
            xSqNorm (extVec2 ψ a₀ a₀) (QA i p) (aOp (Z' i p.2 * X' i p.1))
          ≤ 4 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2) + 2 * cB)
      ∧ (∑ i, w i * ∑ p : A × A,
            xSqNorm (extVec2 ψ a₀ a₀) (QA i p) (aOp (X' i p.1 * Z' i p.2))
          ≤ 4 * (Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2) + 8 * cB) := by
  classical
  -- the two dilations
  obtain ⟨PA, hAsa, hAid, hAsum, hAk⟩ :=
    exists_projective_dilation (d := dA) (A := A × A) (X := ι) a₀
      (E := fun i p => sand (X i) (Z i) p)
      (fun i p => sand_posSemidef (hX i) (hZ i) p) fun i => sum_sand (hX i) (hZ i)
  obtain ⟨PB, hBsa, hBid, hBsum, hBk⟩ :=
    exists_projective_dilation (d := dB) (A := A × A) (X := ι) a₀
      (E := fun i p => sand (X' i) (Z' i) p)
      (fun i p => sand_posSemidef (hX' i) (hZ' i) p) fun i => sum_sand (hX' i) (hZ' i)
  have hPA : ∀ i, IsPVM (PA i) := fun i =>
    { isSelfAdjoint := fun p => by rw [← Matrix.star_eq_conjTranspose, hAsa i p]
      idem := hAid i
      sum_eq_one := hAsum i }
  have hPB : ∀ i, IsPVM (PB i) := fun i =>
    { isSelfAdjoint := fun p => by rw [← Matrix.star_eq_conjTranspose, hBsa i p]
      idem := hBid i
      sum_eq_one := hBsum i }
  -- the chain
  have hchain := one_sub_sum_bornProb_sand_le hw0 hw1 hψ hX hZ hX' hZ' hcA hcB hα hβ
  set Γ : ℝ := Real.sqrt cA + Real.sqrt cB + Real.sqrt (α / 2) + β / 2 with hΓ
  set γ : ι → ℝ := fun i => 1 - ∑ p : A × A,
    bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p) with hγ
  have hγsum : ∑ i, w i * γ i ≤ Γ := by
    rw [hγ, hΓ]
    rw [show (∑ i, w i * (1 - ∑ p : A × A,
          bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p)))
        = 1 - ∑ i, w i * ∑ p : A × A,
          bornProb ψ (sand (X i) (Z i) p) (sand (X' i) (Z' i) p) from by
      rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_sub (w i) 1 _,
        Finset.sum_sub_distrib, Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_one (w i), hw1]]
    exact hchain
  have hB1 : ∀ i, ∑ p : A × A, ‖stateVecB ψ (sand (X' i) (Z' i) p)‖ ^ 2 ≤ 1 := fun i => by
    have h := sum_stateSqNormB_le_one (dA := dA) (B := A × A) hψ (sandPOVM (hX' i) (hZ' i))
    simpa using h
  -- item 1: self-consistency
  have hitem1 : ∀ i, ∑ p : A × A, xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (PB i p) = 2 * γ i :=
    fun i => sum_xSqNorm_dilated_eq hψ a₀ (hPA i) (hPB i) (hAk i) (hBk i)
      (sum_sand (hX i) (hZ i)) (sum_sand (hX' i) (hZ' i))
  -- item 1': against the undilated sandwich
  have hitem1' : ∀ i, ∑ p : A × A,
      xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (sand (X' i) (Z' i) p)) ≤ 2 * γ i := fun i =>
    sum_xSqNorm_dilated_aOp_le hψ a₀ (hPA i) (hAk i) (sum_sand (hX i) (hZ i)) (hB1 i)
  -- the sandwich is close to each ordered product, on Bob's side
  have hord1 : ∀ (i : ι) (p : A × A),
      ‖stateVecB ψ (sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1)‖
        ≤ ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ := by
    intro i p
    rw [show sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1
        = Z' i p.2 * (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) from by
      calc sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1
          = Z' i p.2 * X' i p.1 * Z' i p.2 - Z' i p.2 * Z' i p.2 * X' i p.1 := by
            rw [(hZ' i).idem]; rfl
        _ = Z' i p.2 * (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by noncomm_ring]
    exact norm_stateVecB_mul_le (dA := dA) ψ ((hZ' i).conjTranspose_mul_self_le_one p.2) _
  have hord2 : ∀ (i : ι) (p : A × A),
      ‖stateVecB ψ (sand (X' i) (Z' i) p - X' i p.1 * Z' i p.2)‖
        ≤ 2 * ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ := by
    intro i p
    have hsplit : sand (X' i) (Z' i) p - X' i p.1 * Z' i p.2
        = (sand (X' i) (Z' i) p - Z' i p.2 * X' i p.1)
          - (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1) := by abel
    rw [hsplit, stateVecB_sub']
    refine le_trans (norm_sub_le _ _) ?_
    have h1 := hord1 i p
    linarith
  -- items 2 and 3
  have hitem2 : ∀ i, ∑ p : A × A,
        xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (Z' i p.2 * X' i p.1))
      ≤ 4 * γ i + 2 * ∑ p : A × A,
        ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 := by
    intro i
    have hstep : ∀ p : A × A,
        xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (Z' i p.2 * X' i p.1))
          ≤ 2 * xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (sand (X' i) (Z' i) p))
            + 2 * ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 := by
      intro p
      refine le_trans (xSqNorm_le_of_stateVecB _ _ (aOp (sand (X' i) (Z' i) p)) _) ?_
      have hred : ‖stateVecB (extVec2 ψ a₀ a₀)
            ((aOp (sand (X' i) (Z' i) p) : Matrix (dB × (A × A)) _ ℂ)
              - aOp (Z' i p.2 * X' i p.1))‖
          ≤ ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ := by
        rw [← aOp_sub, norm_stateVecB_extVec2_aOp]
        exact hord1 i p
      have h0 := norm_nonneg (stateVecB (extVec2 ψ a₀ a₀)
        ((aOp (sand (X' i) (Z' i) p) : Matrix (dB × (A × A)) _ ℂ)
          - aOp (Z' i p.2 * X' i p.1)))
      nlinarith [norm_nonneg (stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1))]
    refine le_trans (Finset.sum_le_sum fun p _ => hstep p) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h := hitem1' i
    linarith
  have hitem3 : ∀ i, ∑ p : A × A,
        xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (X' i p.1 * Z' i p.2))
      ≤ 4 * γ i + 8 * ∑ p : A × A,
        ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 := by
    intro i
    have hstep : ∀ p : A × A,
        xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (X' i p.1 * Z' i p.2))
          ≤ 2 * xSqNorm (extVec2 ψ a₀ a₀) (PA i p) (aOp (sand (X' i) (Z' i) p))
            + 8 * ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 := by
      intro p
      refine le_trans (xSqNorm_le_of_stateVecB _ _ (aOp (sand (X' i) (Z' i) p)) _) ?_
      have hred : ‖stateVecB (extVec2 ψ a₀ a₀)
            ((aOp (sand (X' i) (Z' i) p) : Matrix (dB × (A × A)) _ ℂ)
              - aOp (X' i p.1 * Z' i p.2))‖
          ≤ 2 * ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ := by
        rw [← aOp_sub, norm_stateVecB_extVec2_aOp]
        exact hord2 i p
      have h0 := norm_nonneg (stateVecB (extVec2 ψ a₀ a₀)
        ((aOp (sand (X' i) (Z' i) p) : Matrix (dB × (A × A)) _ ℂ)
          - aOp (X' i p.1 * Z' i p.2)))
      nlinarith [norm_nonneg (stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1))]
    refine le_trans (Finset.sum_le_sum fun p _ => hstep p) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h := hitem1' i
    linarith
  refine ⟨PA, PB, hPA, hPB, hAk, hBk, ?_, ?_, ?_⟩
  · rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by rw [hitem1 i]]
    rw [show (∑ i, w i * (2 * γ i)) = 2 * ∑ i, w i * γ i from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring]
    linarith
  · refine le_trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hitem2 i) (hw0 i)) ?_
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_add (w i) (4 * γ i) _,
      Finset.sum_add_distrib,
      show (∑ i, w i * (4 * γ i)) = 4 * ∑ i, w i * γ i from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring,
      show (∑ i, w i * (2 * ∑ p : A × A,
            ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2))
          = 2 * ∑ i, w i * ∑ p : A × A,
            ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring]
    linarith
  · refine le_trans (Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hitem3 i) (hw0 i)) ?_
    rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => mul_add (w i) (4 * γ i) _,
      Finset.sum_add_distrib,
      show (∑ i, w i * (4 * γ i)) = 4 * ∑ i, w i * γ i from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring,
      show (∑ i, w i * (8 * ∑ p : A × A,
            ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2))
          = 8 * ∑ i, w i * ∑ p : A × A,
            ‖stateVecB ψ (X' i p.1 * Z' i p.2 - Z' i p.2 * X' i p.1)‖ ^ 2 from by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring]
    linarith
end MIPRE
