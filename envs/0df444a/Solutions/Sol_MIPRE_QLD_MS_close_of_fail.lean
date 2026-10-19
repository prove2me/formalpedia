-- Prove2me | solution 1 for MIPRE.QLD.MS.close_of_fail
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:36:37.900853+00:00
-- url     : https://prove2.me/submissions/0442de72-be91-477e-91e5-8148290ca84a

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (solution of MIPRE.QLD.MS.close_of_fail);
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
import Theorems.Thm_MIPRE_QLD_MS_one_sub_two_mul_condFail_le_corr
import Theorems.Thm_MIPRE_QLD_MS_qform_eq_corr
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_ancillaEmbed_isometry
import Theorems.Thm_MIPRE_bnd_one_of_conjTranspose_mul_self_le
import Theorems.Thm_MIPRE_condFail_le_div
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
/-- **A rectangular isometry preserves the norm.** -/
theorem norm_evec_mulVec_eq {M : Type*} [Fintype M] {A : Matrix M N ℂ} [DecidableEq N]
    (h : Aᴴ * A = 1) (v : N → ℂ) : ‖evec (A *ᵥ v)‖ = ‖evec v‖ := by
  have hsq : ‖evec (A *ᵥ v)‖ ^ 2 = ‖evec v‖ ^ 2 := by
    rw [norm_evec_mulVec_sq, h, Matrix.one_mulVec, norm_evec_sq]
  nlinarith [norm_nonneg (evec (A *ᵥ v)), norm_nonneg (evec v), hsq]
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
theorem qform_add (M M' : Matrix N N ℂ) : qform v (M + M') = qform v M + qform v M' := by
  rw [qform, qform, qform, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_sub (M M' : Matrix N N ℂ) : qform v (M - M') = qform v M - qform v M' := by
  rw [qform, qform, qform, Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_smul_real (r : ℝ) (M : Matrix N N ℂ) :
    qform v ((r : ℂ) • M) = r * qform v M := by
  rw [qform, qform, Matrix.smul_mulVec, dotProduct_smul]
  simp [Complex.ofReal_re]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
theorem qform_one [DecidableEq N] (hv : ‖evec v‖ = 1) : qform v (1 : Matrix N N ℂ) = 1 := by
  rw [qform, Matrix.one_mulVec, ← norm_evec_sq, hv, one_pow]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
/-- **The squared state norm is the quadratic form of `M† M`.** -/
theorem snorm_sq_eq_qform (M : Matrix N N ℂ) : snorm v M ^ 2 = qform v (Mᴴ * M) := by
  rw [snorm, norm_evec_mulVec_sq, qform]
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

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
theorem V_eq_cells (c : Fin layout.r) : layout.V c = {cell c 0, cell c 1, cell c 2} := by
  fin_cases c <;> decide
end
end MIPRE.LCS.MagicSquare

namespace MIPRE.LCS.MagicSquare
section
open MIPRE.LCS
theorem cell_mem (c : Fin layout.r) (j : Fin 3) : cell c j ∈ layout.V c := by
  rw [V_eq_cells]
  fin_cases j <;> simp
end
end MIPRE.LCS.MagicSquare

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
theorem emb_isometry (dA : Type) [Fintype dA] [DecidableEq dA] :
    (emb dA)ᴴ * emb dA = (1 : Matrix dA dA ℂ) := ancillaEmbed_isometry _
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
theorem norm_dst (ψ : dA × dB → ℂ) : ‖evec (dst ψ)‖ = ‖evec ψ‖ := by
  refine norm_evec_mulVec_eq ?_ ψ
  rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, ← Matrix.mul_kronecker_mul,
    emb_isometry, Matrix.one_mul, Matrix.one_kronecker_one]
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
theorem norm_dst_eq_one {ψ : dA × dB → ℂ} (hψ : star ψ ⬝ᵥ ψ = 1) : ‖evec (dst ψ)‖ = 1 := by
  rw [norm_dst]
  have h : ‖evec ψ‖ ^ 2 = 1 := by rw [norm_evec_sq, hψ, Complex.one_re]
  nlinarith [norm_nonneg (evec ψ), h]
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
variable {ψ : dA × dB → ℂ} {MA : layout.Question → POVM layout.Answer dA}
  {MB : layout.Question → POVM layout.Answer dB}
theorem snorm_sq_le_condFail (hψ : star ψ ⬝ᵥ ψ = 1) (D : Dilated MA) (c : Fin layout.r)
    (j : Fin 3) :
    snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ^ 2
      ≤ 4 * condFail nonlocalGame ψ MA MB (Sum.inl c) (Sum.inr (cell c j)) := by
  have hv : ‖evec (dst ψ)‖ = 1 := norm_dst_eq_one hψ
  set A : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ := aOp (refl D c j) with hA
  set B : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ := bOp (bobs MB (cell c j)) with hB
  have hAsa : Aᴴ = A := by rw [hA, aOp_conjTranspose, refl_conjTranspose]
  have hBsa : Bᴴ = B := by rw [hB, bOp_conjTranspose, bobs_conjTranspose]
  have hAA : A * A = 1 := by rw [hA, ← aOp_mul, refl_mul_self, aOp_one]
  have hcomm : A * B = B * A := by rw [hA, hB, aOp_mul_bOp]
  have hexp : (A - B)ᴴ * (A - B) = 1 - (((2 : ℝ) : ℂ)) • (A * B) + B * B := by
    rw [Matrix.conjTranspose_sub, hAsa, hBsa]
    have h : (A - B) * (A - B) = A * A - A * B - B * A + B * B := by noncomm_ring
    rw [h, hAA, ← hcomm]
    module
  rw [snorm_sq_eq_qform, hexp, qform_add, qform_sub, qform_one _ hv, qform_smul_real]
  have hBB : qform (dst ψ) (B * B) ≤ 1 := by
    have h : qform (dst ψ) (B * B) = snorm (dst ψ) B ^ 2 := by
      rw [snorm_sq_eq_qform, hBsa]
    rw [h]
    have hb : snorm (dst ψ) B ≤ 1 := by
      have := bnd_bobs (dA := dA) (MB := MB) (cell c j) (dst ψ)
      rw [one_mul, hv] at this
      exact this
    nlinarith [snorm_nonneg (dst ψ) B, hb]
  have hcorr := one_sub_two_mul_condFail_le_corr (MA := MA) (MB := MB) hψ c j
  rw [qform_eq_corr]
  linarith
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
variable {ψ : dA × dB → ℂ} {MA : layout.Question → POVM layout.Answer dA}
  {MB : layout.Question → POVM layout.Answer dB}
theorem _root_.solution (hψ : star ψ ⬝ᵥ ψ = 1) (D : Dilated MA) {ε : ℝ} (hε : 0 ≤ ε)
    (hfail : 1 - povmValue nonlocalGame ψ MA MB ≤ ε) :
    ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j)))
      ≤ 12 * Real.sqrt ε := by
  intro c j
  have hμ : nonlocalGame.μ (Sum.inl c) (Sum.inr (cell c j)) = 1 / 36 := by
    have hmem : cell c j ∈ layout.V c := cell_mem c j
    have hcard : (layout.V c).card = 3 := by fin_cases c <;> decide
    rw [nonlocalGame, Game.toNonlocalGame_μ]
    show (if cell c j ∈ layout.V c then 1 / (2 * (layout.r : ℝ) * ((layout.V c).card : ℝ))
      else 0) = 1 / 36
    rw [if_pos hmem, hcard, show ((layout.r : ℕ) : ℝ) = 6 from by norm_num [layout]]
    norm_num
  have hℓ := condFail_le_div (G := nonlocalGame) (MA := MA) (MB := MB) hψ hfail
    (x := Sum.inl c) (y := Sum.inr (cell c j)) (by rw [hμ]; norm_num)
  rw [hμ] at hℓ
  have hsq := snorm_sq_le_condFail (MA := MA) (MB := MB) hψ D c j
  have hsq' : snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ^ 2 ≤ 144 * ε := by
    have : (4 : ℝ) * (ε / (1/36)) = 144 * ε := by ring
    linarith [hsq, hℓ, this]
  have hnn := snorm_nonneg (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j)))
  have hs : Real.sqrt ε * Real.sqrt ε = ε := Real.mul_self_sqrt hε
  nlinarith [hsq', hnn, Real.sqrt_nonneg ε, hs]
end MIPRE.QLD.MS
