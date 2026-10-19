-- Prove2me | solution 1 for MIPRE.QLD.MS.word2
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:36:36.23598+00:00
-- url     : https://prove2.me/submissions/f5f01535-71ea-4b9f-b6eb-c7ceb760fecf

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (solution of MIPRE.QLD.MS.word2);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.CStarMatrix
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import Definitions.Def_MIPRE_Foundations_Games
import Definitions.Def_MIPRE_Foundations_Distances
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_OpBound_B
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_StateDistance_B
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_PVM_B
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_RegisterReindex_B
import Definitions.Def_MIPRE_LCS_Basic
import Definitions.Def_MIPRE_LCS_Common
import Definitions.Def_MIPRE_LCS_Measurement
import Definitions.Def_MIPRE_LCS_Observable
import Definitions.Def_MIPRE_LCS_Strategy_ObservableToProjector
import Definitions.Def_MIPRE_LCS_NonlocalGame
import Definitions.Def_MIPRE_LCS_Pauli
import Definitions.Def_MIPRE_LCS_MagicSquare_Strategy
import Definitions.Def_MIPRE_LCS_MagicSquare_Game
import Definitions.Def_MIPRE_Foundations_Swap
import Definitions.Def_MIPRE_Background_QLD_Anticomm
import Theorems.Thm_MIPRE_POVM_sub_mul_self_le_one
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_bnd_one_of_conjTranspose_mul_self_le
import Theorems.Thm_MIPRE_pvmObs_mul
import Theorems.Thm_MIPRE_star_sgn

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
/-- The sesquilinear form of two matrices applied to the same vector, moved onto one side:
`⟨A v, B v⟩ = ⟨v, A† B v⟩`. -/
theorem star_mulVec_dotProduct {M : Type*} [Fintype M] (A B : Matrix M N ℂ) (v : N → ℂ) :
    star (A *ᵥ v) ⬝ᵥ (B *ᵥ v) = star v ⬝ᵥ ((Aᴴ * B) *ᵥ v) := by
  rw [Matrix.star_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.dotProduct_mulVec]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_sq (v : N → ℂ) : ‖evec v‖ ^ 2 = (star v ⬝ᵥ v).re := by
  classical
  rw [evec, EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _),
    dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : star v i * v i = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
    rw [Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
    norm_cast
  rw [h, Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem norm_evec_mulVec_sq {M : Type*} [Fintype M] (A : Matrix M N ℂ) (v : N → ℂ) :
    ‖evec (A *ᵥ v)‖ ^ 2 = (star v ⬝ᵥ ((Aᴴ * A) *ᵥ v)).re := by
  rw [norm_evec_sq, star_mulVec_dotProduct]
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
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
/-- An isometry preserves the norm exactly. -/
theorem norm_evec_mulVec_of_isometry {M : Matrix N N ℂ} (h : Mᴴ * M = 1) (v : N → ℂ) :
    ‖evec (M *ᵥ v)‖ = ‖evec v‖ := by
  have hsq : ‖evec (M *ᵥ v)‖ ^ 2 = ‖evec v‖ ^ 2 := by
    rw [norm_evec_mulVec_sq, h, Matrix.one_mulVec, norm_evec_sq]
  have h1 : (0 : ℝ) ≤ ‖evec (M *ᵥ v)‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖evec v‖ := norm_nonneg _
  nlinarith [hsq]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
theorem bnd_one_of_isometry {M : Matrix N N ℂ} (h : Mᴴ * M = 1) : Bnd M 1 := fun v => by
  rw [norm_evec_mulVec_of_isometry h v, one_mul]
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
open Finset Matrix
open scoped ComplexOrder MatrixOrder
open Kronecker
set_option linter.unusedSectionVars false
variable {N : Type*} [Fintype N]
variable [DecidableEq N]
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
/-- An isometry on the first factor is an isometry on the product space. -/
theorem isometry_aOp {X : Matrix HA HA ℂ} (h : Xᴴ * X = 1) :
    ((aOp X : Matrix (HA × HB) _ ℂ))ᴴ * aOp X = 1 := by
  rw [aOp_conjTranspose, ← aOp_mul, h, aOp_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix Kronecker
open scoped ComplexOrder MatrixOrder
/-- The difference of two POVM elements is self-adjoint. -/
theorem POVM.sub_conjTranspose {A d : Type*} [Fintype A] [Fintype d] [DecidableEq d]
    (M : POVM A d) (p q : A) :
    (((M.mats p).val - (M.mats q).val))ᴴ = ((M.mats p).val - (M.mats q).val) := by
  rw [Matrix.conjTranspose_sub, ← Matrix.star_eq_conjTranspose, ← Matrix.star_eq_conjTranspose,
    (M.mats p).2, (M.mats q).2]
end
end MIPRE

namespace MIPRE
noncomputable section
theorem sgn_mul_self (x : ZMod 2) : sgn x * sgn x = 1 := by
  rw [sgn]; split_ifs <;> norm_num
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
omit [DecidableEq Λ] in
theorem pvmObs_const (h : IsPVM P) (c : ℂ) :
    pvmObs P (fun _ => c) = c • (1 : Matrix n n ℂ) := by
  rw [pvmObs, ← Finset.smul_sum, h.sum_eq_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
omit [DecidableEq Λ] in
theorem pvmObs_one (h : IsPVM P) : pvmObs P 1 = (1 : Matrix n n ℂ) := by
  rw [show (1 : Λ → ℂ) = fun _ => (1 : ℂ) from rfl, pvmObs_const h, one_smul]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
omit [DecidableEq Λ] in
theorem pvmObs_conjTranspose (h : IsPVM P) (ε : Λ → ℂ) :
    (pvmObs P ε)ᴴ = pvmObs P (star ε) := by
  rw [pvmObs, pvmObs, Matrix.conjTranspose_sum]
  exact Finset.sum_congr rfl fun a _ => by
    rw [Matrix.conjTranspose_smul, h.isSelfAdjoint]
    rfl
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
omit [DecidableEq Λ] in
/-- A real weighting gives a self-adjoint operator. -/
theorem pvmObs_isSelfAdjoint (h : IsPVM P) {ε : Λ → ℂ} (hε : ∀ a, star (ε a) = ε a) :
    (pvmObs P ε)ᴴ = pvmObs P ε := by
  rw [pvmObs_conjTranspose h]
  congr 1
  funext a
  exact hε a
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
/-- A weighting squaring to one pointwise gives an operator squaring to one. -/
theorem pvmObs_mul_self (h : IsPVM P) {ε : Λ → ℂ} (hε : ∀ a, ε a * ε a = 1) :
    pvmObs P ε * pvmObs P ε = 1 := by
  rw [pvmObs_mul h]
  rw [show ε * ε = 1 from funext fun a => hε a]
  exact pvmObs_one h
end
end MIPRE

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
theorem csgn_mul_self (c : Fin layout.r) (j : Fin 3) (k : PV) :
    csgn c j k * csgn c j k = 1 := sgn_mul_self _
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
theorem star_csgn (c : Fin layout.r) (j : Fin 3) (k : PV) :
    star (csgn c j k) = csgn c j k := star_sgn _
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
theorem refl_conjTranspose (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    (refl D c j)ᴴ = refl D c j :=
  pvmObs_isSelfAdjoint (D.isPVM c) fun k => star_csgn c j k
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
theorem refl_mul_self (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    refl D c j * refl D c j = 1 :=
  pvmObs_mul_self (D.isPVM c) fun k => csgn_mul_self c j k
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
theorem bobs_conjTranspose (j : Fin layout.s) : (bobs MB j)ᴴ = bobs MB j :=
  POVM.sub_conjTranspose _ _ _
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
theorem bnd_bobs (j : Fin layout.s) :
    Bnd (bOp (bobs MB j) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 := by
  refine bnd_bOp ?_
  rw [bobs_conjTranspose]
  exact POVM.sub_mul_self_le_one _ _ _
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
theorem alice_isometry (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    ((aOp (refl D c j) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ))ᴴ * aOp (refl D c j) = 1 := by
  refine isometry_aOp ?_
  rw [refl_conjTranspose]
  exact refl_mul_self D c j
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
theorem bnd_alice (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    Bnd (aOp (refl D c j) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 :=
  bnd_one_of_isometry (alice_isometry D c j)
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}
theorem word1 (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c : Fin layout.r) (j : Fin 3) :
    snorm (dst ψ) (bOp (bobs MB (cell c j)) - aOp (refl D c j)) ≤ γ := by
  rw [snorm_sub_comm]
  exact hγ c j
end
end MIPRE.QLD.MS

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.QLD.MS
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}
theorem _root_.solution (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c c' : Fin layout.r) (i j : Fin 3) :
    snorm (dst ψ) (bOp (bobs MB (cell c i) * bobs MB (cell c' j))
      - aOp (refl D c' j * refl D c i)) ≤ 2 * γ := by
  have h1 : (aOp (refl D c' j) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      * bOp (bobs MB (cell c i)) = bOp (bobs MB (cell c i)) * aOp (refl D c' j) :=
    aOp_mul_bOp _ _
  have hsplit : (bOp (bobs MB (cell c i) * bobs MB (cell c' j))
        - aOp (refl D c' j * refl D c i) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = bOp (bobs MB (cell c i)) * (bOp (bobs MB (cell c' j)) - aOp (refl D c' j))
        + aOp (refl D c' j) * (bOp (bobs MB (cell c i)) - aOp (refl D c i)) := by
    rw [bOp_mul, aOp_mul, mul_sub, mul_sub, h1]
    abel
  rw [hsplit]
  refine le_trans (snorm_add_le _ _ _) ?_
  have hb := snorm_mul_le (dst ψ) (bnd_bobs (dA := dA) (MB := MB) (cell c i))
    (bOp (bobs MB (cell c' j)) - aOp (refl D c' j))
  have ha := snorm_mul_le (dst ψ) (bnd_alice (dB := dB) D c' j)
    (bOp (bobs MB (cell c i)) - aOp (refl D c i))
  have hw1 := word1 hγ c' j
  have hw2 := word1 hγ c i
  linarith
end MIPRE.QLD.MS
