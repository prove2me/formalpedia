-- Prove2me | solution 1 for MIPRE.norm_stateVec_anticomm_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:32:22.884913+00:00
-- url     : https://prove2.me/submissions/114be7c2-b959-4db4-a273-62ec6ebcc036

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/CrossConsistency.lean (solution of MIPRE.norm_stateVec_anticomm_le);
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
import Theorems.Thm_MIPRE_aOp_add
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_aOp_sub
import Theorems.Thm_MIPRE_bnd_one_of_conjTranspose_mul_self_le

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
/-- A contraction on the first factor is a contraction on the product space. -/
theorem bnd_aOp {X : Matrix HA HA ℂ} (h : (Xᴴ * X) ≤ (1 : Matrix HA HA ℂ)) :
    Bnd (aOp X : Matrix (HA × HB) _ ℂ) 1 := by
  refine bnd_one_of_conjTranspose_mul_self_le ?_
  rw [aOp_conjTranspose, ← aOp_mul, ← aOp_one (HA := HA) (HB := HB)]
  refine sub_nonneg.mp ?_
  rw [← aOp_sub]
  exact aOp_nonneg (sub_nonneg.mpr h)
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
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- The deviation is the state-norm of the single operator `A ⊗ Id - Id ⊗ B` on the product
space, which is what the operator-norm calculus of `MIPRE/Foundations/OpBound.lean` consumes. -/
theorem xNorm_eq_snorm (ψ : dA × dB → ℂ) (A : Matrix dA dA ℂ) (B : Matrix dB dB ℂ) :
    xNorm ψ A B = snorm ψ ((aOp A : Matrix (dA × dB) _ ℂ) - bOp B) := by
  rw [xNorm, snorm, Matrix.sub_mulVec, evec_sub]
  rfl
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
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
/-- **The order-reversal rule.** If `A ⊗ Id` is `K`-boundedly close to `Id ⊗ A'` and `B ⊗ Id` to
`Id ⊗ B'`, then `AB ⊗ Id` is close to `Id ⊗ B'A'`: Bob's factors appear in the opposite order,
and each deviation is paid for by the operator norm of the factor in front of it. -/
theorem xNorm_mul_le {K L : ℝ} (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
    (hA : Bnd (aOp A : Matrix (dA × dB) _ ℂ) K) (hB' : Bnd (bOp B' : Matrix (dA × dB) _ ℂ) L) :
    xNorm ψ (A * B) (B' * A') ≤ K * xNorm ψ B B' + L * xNorm ψ A A' := by
  have hsplit : (aOp (A * B) : Matrix (dA × dB) _ ℂ) - bOp (B' * A')
      = (aOp A : Matrix (dA × dB) _ ℂ) * ((aOp B : Matrix (dA × dB) _ ℂ) - bOp B')
        + (bOp B' : Matrix (dA × dB) _ ℂ) * ((aOp A : Matrix (dA × dB) _ ℂ) - bOp A') := by
    rw [aOp_mul, bOp_mul, Matrix.mul_sub, Matrix.mul_sub, aOp_mul_bOp A B']
    abel
  rw [xNorm_eq_snorm, xNorm_eq_snorm, xNorm_eq_snorm, hsplit]
  refine le_trans (snorm_add_le ψ _ _) (add_le_add ?_ ?_)
  · exact snorm_mul_le ψ hA _
  · exact snorm_mul_le ψ hB' _
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
/-- The order reversal for contractions, which is how every consumer uses it: POVM elements and
generalized observables are bounded by one on either factor. -/
theorem xNorm_mul_le_one (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
    (hA : Aᴴ * A ≤ (1 : Matrix dA dA ℂ)) (hB' : B'ᴴ * B' ≤ (1 : Matrix dB dB ℂ)) :
    xNorm ψ (A * B) (B' * A') ≤ xNorm ψ B B' + xNorm ψ A A' := by
  have h := xNorm_mul_le (ψ := ψ) A B A' B' (bnd_aOp hA) (bnd_bOp hB')
  rwa [one_mul, one_mul] at h
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
variable {X Y A B C dA dB : Type*} [Fintype X] [Fintype Y] [Fintype A] [Fintype B]
  [Fintype C] [DecidableEq C] [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {G : Game X Y A B} {ψ : dA × dB → ℂ} {MA : X → POVM A dA} {MB : Y → POVM B dB}
variable {ε : ℝ}
variable {ψ : dA × dB → ℂ}
theorem _root_.solution (A B : Matrix dA dA ℂ) (A' B' : Matrix dB dB ℂ)
    (hA : Aᴴ * A ≤ (1 : Matrix dA dA ℂ)) (hB : Bᴴ * B ≤ (1 : Matrix dA dA ℂ))
    (hA' : A'ᴴ * A' ≤ (1 : Matrix dB dB ℂ)) (hB' : B'ᴴ * B' ≤ (1 : Matrix dB dB ℂ)) :
    ‖stateVec ψ (A * B + B * A)‖
      ≤ 2 * xNorm ψ A A' + 2 * xNorm ψ B B' + ‖stateVecB ψ (A' * B' + B' * A')‖ := by
  have hsplit : (aOp (A * B + B * A) : Matrix (dA × dB) _ ℂ)
      = ((aOp (A * B) : Matrix (dA × dB) _ ℂ) - bOp (B' * A'))
        + (bOp (A' * B' + B' * A') : Matrix (dA × dB) _ ℂ)
        + ((aOp (B * A) : Matrix (dA × dB) _ ℂ) - bOp (A' * B')) := by
    rw [aOp_add, bOp_add]
    abel
  have e1 : snorm ψ (((aOp (A * B) : Matrix (dA × dB) _ ℂ) - bOp (B' * A')
        + bOp (A' * B' + B' * A')) + ((aOp (B * A) : Matrix (dA × dB) _ ℂ) - bOp (A' * B')))
      ≤ snorm ψ ((aOp (A * B) : Matrix (dA × dB) _ ℂ) - bOp (B' * A')
          + bOp (A' * B' + B' * A'))
        + snorm ψ ((aOp (B * A) : Matrix (dA × dB) _ ℂ) - bOp (A' * B')) :=
    snorm_add_le ψ _ _
  have e2 : snorm ψ ((aOp (A * B) : Matrix (dA × dB) _ ℂ) - bOp (B' * A')
        + bOp (A' * B' + B' * A'))
      ≤ snorm ψ ((aOp (A * B) : Matrix (dA × dB) _ ℂ) - bOp (B' * A'))
        + snorm ψ (bOp (A' * B' + B' * A') : Matrix (dA × dB) _ ℂ) :=
    snorm_add_le ψ _ _
  have e3 : snorm ψ ((aOp (A * B) : Matrix (dA × dB) _ ℂ) - bOp (B' * A'))
      = xNorm ψ (A * B) (B' * A') := (xNorm_eq_snorm ψ _ _).symm
  have e4 : snorm ψ ((aOp (B * A) : Matrix (dA × dB) _ ℂ) - bOp (A' * B'))
      = xNorm ψ (B * A) (A' * B') := (xNorm_eq_snorm ψ _ _).symm
  have e5 : snorm ψ (bOp (A' * B' + B' * A') : Matrix (dA × dB) _ ℂ)
      = ‖stateVecB ψ (A' * B' + B' * A')‖ := (norm_stateVecB_eq_snorm ψ _).symm
  have h1 : xNorm ψ (A * B) (B' * A') ≤ xNorm ψ B B' + xNorm ψ A A' :=
    xNorm_mul_le_one A B A' B' hA hB'
  have h2 : xNorm ψ (B * A) (A' * B') ≤ xNorm ψ A A' + xNorm ψ B B' :=
    xNorm_mul_le_one B A B' A' hB hA'
  rw [norm_stateVec_eq_snorm, hsplit]
  linarith
end MIPRE
