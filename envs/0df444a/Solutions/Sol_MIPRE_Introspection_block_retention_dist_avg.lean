-- Prove2me | solution 1 for MIPRE.Introspection.block_retention_dist_avg
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:32:41.719169+00:00
-- url     : https://prove2.me/submissions/2e9337af-5a7e-4337-87d1-6cc2a5533b8d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/BlockRetention.lean (solution of MIPRE.Introspection.block_retention_dist_avg);
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
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
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
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Theorems.Thm_MIPRE_Introspection_retained_block_le_completion
import Theorems.Thm_MIPRE_Introspection_retained_fibre_dist
import Theorems.Thm_MIPRE_Introspection_submeasurement_completion_dist_avg
import Theorems.Thm_MIPRE_IsPVM_aOp
import Theorems.Thm_MIPRE_IsPVM_orthogonal
import Theorems.Thm_MIPRE_IsPVM_posSemidef
import Theorems.Thm_MIPRE_POVM_sum_val
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_aOp_sum

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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
/-- **The two factors commute.** -/
theorem aOp_mul_bOp (X : Matrix HA HA ℂ) (Y : Matrix HB HB ℂ) :
    (aOp X : Matrix (HA × HB) _ ℂ) * bOp Y = bOp Y * aOp X := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.one_mul,
    Matrix.mul_one, Matrix.one_mul, Matrix.mul_one]
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
theorem aOp_nonneg {X : Matrix HA HA ℂ} (hX : (0 : Matrix HA HA ℂ) ≤ X) :
    (0 : Matrix (HA × HB) (HA × HB) ℂ) ≤ aOp X :=
  Matrix.nonneg_iff_posSemidef.mpr
    ((Matrix.nonneg_iff_posSemidef.mp hX).kronecker (Matrix.PosSemidef.one))
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

namespace MIPRE.IsPVM
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
/-- `P a * P b` is `P a` on the diagonal and zero off it. -/
theorem mul_eq_ite (h : IsPVM P) (a b : Λ) :
    P a * P b = if a = b then P a else 0 := by
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl, h.idem]
  · rw [if_neg hab, h.orthogonal hab]
end
end MIPRE.IsPVM

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem aOp_mono {X Y : Matrix dA dA ℂ} (h : X ≤ Y) :
    (aOp X : Matrix (dA × dB) _ ℂ) ≤ aOp Y := by
  rw [← sub_nonneg, ← aOp_sub]
  exact aOp_nonneg (sub_nonneg.mpr h)
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
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {R1 R2 : Type*} [Fintype R1] [DecidableEq R1] [Fintype R2] [DecidableEq R2]
theorem IsPVM.bOp {ι : Type*} [Fintype ι] {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    IsPVM fun i => (bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ) where
  isSelfAdjoint i := by rw [bOp_conjTranspose, h.isSelfAdjoint]
  idem i := by rw [← bOp_mul, h.idem]
  sum_eq_one := by rw [← bOp_sum, h.sum_eq_one, bOp_one]
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
/-- Multiplication by a readout projector retains exactly its own block. -/
theorem sum_blocks_mul_readout (P : Y → Matrix V V ℂ) (hP : IsPVM P)
    (Q : Y → Matrix H H ℂ) (y : Y) :
    (∑ z, P z ⊗ₖ Q z) * aOp (P y) = P y ⊗ₖ Q y := by
  rw [Finset.sum_mul]
  have hterm z : (P z ⊗ₖ Q z) * aOp (P y) = (P z * P y) ⊗ₖ Q z := by
    rw [aOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one]
  simp_rw [hterm, hP.mul_eq_ite]
  rw [Finset.sum_eq_single y]
  · simp
  · intro z _ hzy
    simp [hzy]
  · simp
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
variable {B : Type*} [Fintype B] [DecidableEq B]
/-- Retain the matching ancillary block, using the exactly consistent mirror readout. -/
theorem block_retention_precompletion (ψ : (V × H) × B → ℂ)
    (M : Y × A → Matrix (V × H) (V × H) ℂ) (hM : IsPVM M)
    (P : Y → Matrix V V ℂ) (hP : IsPVM P) (Q : Y → POVM (Y × A) H)
    (R : Y → Matrix B B ℂ) (hR : IsPVM R)
    (hPR : ∀ y, aOp (aOp (P y) : Matrix (V × H) _ ℂ) *ᵥ ψ = bOp (R y) *ᵥ ψ) :
    (∑ p : Y × A, stateSqNorm ψ (M p - P p.1 ⊗ₖ ((Q p.1).mats p).val)) ≤
      2 * (∑ y, stateSqNorm ψ ((∑ a, M (y, a)) - aOp (P y))) +
      2 * (∑ p : Y × A, stateSqNorm ψ (M p - ∑ z, P z ⊗ₖ ((Q z).mats p).val)) := by
  have h := retained_fibre_dist ψ (fun p => aOp (M p))
    (fun p => aOp (∑ z, P z ⊗ₖ ((Q z).mats p).val)) (fun y => aOp (aOp (P y)))
    (fun y => bOp (R y)) hM.aOp hR.bOp hPR
    (fun y a => aOp_mul_bOp _ _) (fun y a => aOp_mul_bOp _ _)
  simp only [← aOp_mul, sum_blocks_mul_readout P hP, ← aOp_sub, ← aOp_sum] at h
  simpa only [stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using h
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Classical
open scoped Kronecker ComplexOrder MatrixOrder
variable {V H Y A : Type*} [Fintype V] [DecidableEq V] [Fintype H] [DecidableEq H]
  [Fintype Y] [DecidableEq Y] [Fintype A] [DecidableEq A]
variable {B : Type*} [Fintype B] [DecidableEq B]
theorem _root_.solution {X : Type*} [Fintype X]
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (ψ : (V × H) × B → ℂ) (hψ : ‖evec ψ‖ = 1)
    (M : X → Y × A → Matrix (V × H) (V × H) ℂ) (hM : ∀ x, IsPVM (M x))
    (P : X → Y → Matrix V V ℂ) (hP : ∀ x, IsPVM (P x))
    (Q : X → Y → POVM (Y × A) H) (R : X → Y → Matrix B B ℂ) (hR : ∀ x, IsPVM (R x))
    (hPR : ∀ x y, aOp (aOp (P x y) : Matrix (V × H) _ ℂ) *ᵥ ψ = bOp (R x y) *ᵥ ψ)
    {δ : ℝ} (hclose : ∑ x, D x *
      (2 * (∑ y, stateSqNorm ψ ((∑ a, M x (y, a)) - aOp (P x y))) +
       2 * (∑ p : Y × A, stateSqNorm ψ (M x p - ∑ z, P x z ⊗ₖ ((Q x z).mats p).val))) ≤ δ) :
    (∑ x, D x * ∑ p : Y × A, stateSqNorm ψ
      (M x p - P x p.1 ⊗ₖ (((Q x p.1).map Prod.snd).mats p.2).val)) ≤
      2 * δ + 4 * Real.sqrt δ := by
  let Bb x (p : Y × A) := P x p.1 ⊗ₖ ((Q x p.1).mats p).val
  let Cc x := controlledPOVM (P x) (hP x) (fun y => (Q x y).map Prod.snd)
  have hret := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left
      (block_retention_precompletion ψ (M x) (hM x) (P x) (hP x) (Q x) (R x) (hR x)
        (hPR x)) (hD0 x)
  have hret' : ∑ x, D x * ∑ p : Y × A, snorm ψ (aOp (M x p) - aOp (Bb x p)) ^ 2 ≤ δ := by
    simpa only [← aOp_sub, Bb, stateSqNorm, stateNorm, norm_stateVec_eq_snorm] using
      hret.trans hclose
  have h := submeasurement_completion_dist_avg D hD0 hD1 ψ hψ
    (fun x p => aOp (M x p)) (fun x p => aOp (Bb x p))
    (fun x p => aOp (((Cc x).mats p).val)) (fun x => (hM x).aOp)
    (fun x p => aOp_nonneg (((hP x).posSemidef p.1).kronecker
      (Matrix.nonneg_iff_posSemidef.mp (Subtype.coe_le_coe.mpr ((Q x p.1).nonneg p)))).nonneg)
    (fun x p => aOp_nonneg (Subtype.coe_le_coe.mpr ((Cc x).nonneg p)))
    (fun x => by rw [← aOp_sum, POVM.sum_val, aOp_one])
    (fun x p => aOp_mono (retained_block_le_completion (P x) (hP x) (Q x) p)) hret'
  simpa only [← aOp_sub, stateSqNorm, stateNorm, norm_stateVec_eq_snorm,
    Cc, controlledPOVM] using h
end MIPRE.Introspection
