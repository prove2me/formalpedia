-- Prove2me | solution 1 for MIPRE.QLD.MS.snorm_anti
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:40:10.802685+00:00
-- url     : https://prove2.me/submissions/8f328173-bb73-402e-851c-8fb533f17813

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (solution of MIPRE.QLD.MS.snorm_anti);
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
import Theorems.Thm_MIPRE_QLD_MS_bnd_one_sub_sq
import Theorems.Thm_MIPRE_QLD_MS_path
import Theorems.Thm_MIPRE_QLD_MS_snorm_one_sub_sq
import Theorems.Thm_MIPRE_QLD_MS_word2
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
theorem Bnd.add {M M' : Matrix N N ℂ} {K L : ℝ} (h : Bnd M K) (h' : Bnd M' L) :
    Bnd (M + M') (K + L) := fun v => by
  rw [Matrix.add_mulVec, evec_add]
  refine le_trans (norm_add_le _ _) ?_
  rw [add_mul]
  exact add_le_add (h v) (h' v)
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
theorem Bnd.mul {M M' : Matrix N N ℂ} {K L : ℝ} (hK : 0 ≤ K) (h : Bnd M K) (h' : Bnd M' L) :
    Bnd (M * M') (K * L) := fun v => by
  rw [← Matrix.mulVec_mulVec]
  refine le_trans (h (M' *ᵥ v)) ?_
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h' v) hK
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
variable (v : N → ℂ)
/-- An isometry in front changes nothing. -/
theorem snorm_mul_of_isometry [DecidableEq N] {M : Matrix N N ℂ} (h : Mᴴ * M = 1)
    (M' : Matrix N N ℂ) :
    snorm v (M * M') = snorm v M' := by
  rw [snorm, snorm, ← Matrix.mulVec_mulVec, norm_evec_mulVec_eq h]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {N : Type*} [Fintype N]
variable (v : N → ℂ)
/-- **Replacing an operator by an isometry it is close to, in front of anything.** If `W` and
the isometry `WD` agree on the state to within `δ`, and `WD` commutes with `Z`, then `Z W` is
within `K δ` of `Z`, where `K` bounds `Z`. This is the suffix-insertion bound of the Magic
Square argument, and it is the only place the commutation of the two parties is used. -/
theorem snorm_mul_swap [DecidableEq N] {W WD Z : Matrix N N ℂ} {δ K : ℝ}
    (hWD : WDᴴ * WD = 1) (hcomm : WD * Z = Z * WD) (hZ : Bnd Z K) (hK : 0 ≤ K)
    (hd : snorm v (W - WD) ≤ δ) :
    snorm v (Z * W) ≤ snorm v Z + K * δ := by
  have hsplit : Z * W = Z * (W - WD) + WD * Z := by
    have h : Z * (W - WD) + WD * Z = Z * (W - WD) + Z * WD := by rw [hcomm]
    rw [h]
    noncomm_ring
  calc snorm v (Z * W) ≤ snorm v (Z * (W - WD)) + snorm v (WD * Z) := by
        rw [hsplit]; exact snorm_add_le v _ _
    _ ≤ K * δ + snorm v Z := by
        refine add_le_add ?_ (le_of_eq (snorm_mul_of_isometry v hWD Z))
        exact le_trans (snorm_mul_le v hZ _) (mul_le_mul_of_nonneg_left hd hK)
    _ = snorm v Z + K * δ := by ring
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
/-- A product of Bob observables is a contraction. -/
theorem bnd_bobs_mul (X Y : Matrix dB dB ℂ)
    (hX : Bnd (bOp X : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1)
    (hY : Bnd (bOp Y : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1) :
    Bnd (bOp (X * Y) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 := by
  rw [bOp_mul]
  simpa using Bnd.mul (by norm_num : (0:ℝ) ≤ 1) hX hY
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

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}
theorem word3 (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c c' c'' : Fin layout.r) (i j k : Fin 3) :
    snorm (dst ψ) (bOp (bobs MB (cell c i) * bobs MB (cell c' j) * bobs MB (cell c'' k))
      - aOp (refl D c'' k * (refl D c' j * refl D c i))) ≤ 3 * γ := by
  have hcomm : (aOp (refl D c'' k) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      * bOp (bobs MB (cell c i) * bobs MB (cell c' j))
      = bOp (bobs MB (cell c i) * bobs MB (cell c' j)) * aOp (refl D c'' k) :=
    aOp_mul_bOp _ _
  have hsplit : (bOp (bobs MB (cell c i) * bobs MB (cell c' j) * bobs MB (cell c'' k))
        - aOp (refl D c'' k * (refl D c' j * refl D c i))
          : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = bOp (bobs MB (cell c i) * bobs MB (cell c' j))
          * (bOp (bobs MB (cell c'' k)) - aOp (refl D c'' k))
        + aOp (refl D c'' k)
          * (bOp (bobs MB (cell c i) * bobs MB (cell c' j))
              - aOp (refl D c' j * refl D c i)) := by
    rw [bOp_mul (bobs MB (cell c i) * bobs MB (cell c' j)), aOp_mul (refl D c'' k), mul_sub,
      mul_sub, hcomm]
    abel
  rw [hsplit]
  refine le_trans (snorm_add_le _ _ _) ?_
  have hbb := bnd_bobs_mul (dA := dA) (bobs MB (cell c i)) (bobs MB (cell c' j))
    (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  have hb := snorm_mul_le (dst ψ) hbb (bOp (bobs MB (cell c'' k)) - aOp (refl D c'' k))
  have ha := snorm_mul_le (dst ψ) (bnd_alice (dB := dB) D c'' k)
    (bOp (bobs MB (cell c i) * bobs MB (cell c' j)) - aOp (refl D c' j * refl D c i))
  have hw1 := word1 hγ c'' k
  have hw2 := word2 hγ c c' i j
  linarith
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
theorem refl_isometry (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    (refl D c j)ᴴ * refl D c j = 1 := by
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
variable {ψ : dA × dB → ℂ} {D : Dilated MA} {γ : ℝ}
theorem isometry_mul {X Y : Matrix (dA × PV) (dA × PV) ℂ} (hX : Xᴴ * X = 1) (hY : Yᴴ * Y = 1) :
    (X * Y)ᴴ * (X * Y) = 1 := by
  rw [Matrix.conjTranspose_mul]
  calc Yᴴ * Xᴴ * (X * Y) = Yᴴ * (Xᴴ * X) * Y := by simp only [mul_assoc]
    _ = Yᴴ * Y := by rw [hX, mul_one]
    _ = 1 := hY
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
theorem bnd_anti :
    Bnd (bOp (anti MB) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 2 := by
  rw [anti, bOp_add]
  have h1 := bnd_bobs_mul (dA := dA) (bobs MB (var 0)) (bobs MB (var 4))
    (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  have h2 := bnd_bobs_mul (dA := dA) (bobs MB (var 4)) (bobs MB (var 0))
    (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  have h := Bnd.add h1 h2
  rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
  exact h
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
theorem _root_.solution
    (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ) :
    snorm (dst ψ) (bOp (anti MB) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 36 * γ := by
  have c02 : cell (con 0) 2 = var 2 := rfl
  have c10 : cell (con 1) 0 = var 3 := rfl
  have c11 : cell (con 1) 1 = var 4 := rfl
  have c40 : cell (con 4) 0 = var 1 := rfl
  have c41 : cell (con 4) 1 = var 4 := rfl
  have c30 : cell (con 3) 0 = var 0 := rfl
  -- the word `T = (a e + e a) b`
  set T : Matrix dB dB ℂ := anti MB * bobs MB (var 1) with hT
  -- step A: the path, rearranged
  have hA : snorm (dst ψ) (bOp (bobs MB (var 3) * T)
      : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 24 * γ := by
    have h := path hγ
    rw [dd] at h
    rw [show (bOp (bobs MB (var 3) * T) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
        = bOp (bobs MB (var 3) * bobs MB (var 0) * (bobs MB (var 4) * bobs MB (var 1)))
          - bOp (-(bobs MB (var 3) * bobs MB (var 4)
              * (bobs MB (var 0) * bobs MB (var 1)))) from by
      rw [← bOp_sub]
      congr 1
      rw [hT, anti]
      noncomm_ring]
    exact h
  -- step B: the two length-three words, with `Id - b₃²` in front
  have hB : snorm (dst ψ) (bOp ((1 - bobs MB (var 3) * bobs MB (var 3)) * T)
      : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 10 * γ := by
    have hz := snorm_one_sub_sq (D := D) hγ (con 1) 0
    rw [c10] at hz
    have hzb := bnd_one_sub_sq (dA := dA) (MB := MB) (var 3)
    have hstep : ∀ (X Y Z : Matrix dB dB ℂ) (cX cY cZ : Fin layout.r) (iX iY iZ : Fin 3),
        X = bobs MB (cell cX iX) → Y = bobs MB (cell cY iY) → Z = bobs MB (cell cZ iZ) →
        snorm (dst ψ) (bOp ((1 - bobs MB (var 3) * bobs MB (var 3)) * (X * Y * Z))
          : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 5 * γ := by
      intro X Y Z cX cY cZ iX iY iZ hX hY hZ
      subst hX; subst hY; subst hZ
      have hw := word3 hγ cX cY cZ iX iY iZ
      have hcomm : (aOp (refl D cZ iZ * (refl D cY iY * refl D cX iX))
            : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
          * bOp (1 - bobs MB (var 3) * bobs MB (var 3))
          = bOp (1 - bobs MB (var 3) * bobs MB (var 3))
            * aOp (refl D cZ iZ * (refl D cY iY * refl D cX iX)) := aOp_mul_bOp _ _
      have hiso := isometry_mul (refl_isometry D cZ iZ)
        (isometry_mul (refl_isometry D cY iY) (refl_isometry D cX iX))
      have h := snorm_mul_swap (dst ψ) (isometry_aOp hiso) hcomm hzb (by norm_num) hw
      rw [← bOp_mul] at h
      linarith
    have h1 := hstep (bobs MB (var 0)) (bobs MB (var 4)) (bobs MB (var 1))
      (con 3) (con 1) (con 4) 0 1 0 (congrArg (bobs MB) c30.symm)
      (congrArg (bobs MB) c11.symm) (congrArg (bobs MB) c40.symm)
    have h2 := hstep (bobs MB (var 4)) (bobs MB (var 0)) (bobs MB (var 1))
      (con 1) (con 3) (con 4) 1 0 0 (congrArg (bobs MB) c11.symm)
      (congrArg (bobs MB) c30.symm) (congrArg (bobs MB) c40.symm)
    have hsplit : ((1 : Matrix dB dB ℂ) - bobs MB (var 3) * bobs MB (var 3)) * T
        = (1 - bobs MB (var 3) * bobs MB (var 3))
            * (bobs MB (var 0) * bobs MB (var 4) * bobs MB (var 1))
          + (1 - bobs MB (var 3) * bobs MB (var 3))
            * (bobs MB (var 4) * bobs MB (var 0) * bobs MB (var 1)) := by
      rw [hT, anti]
      noncomm_ring
    rw [hsplit, bOp_add]
    refine le_trans (snorm_add_le _ _ _) ?_
    linarith
  -- step C: `T` itself
  have hC : snorm (dst ψ) (bOp T : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      ≤ 34 * γ := by
    have hsplit : T = (1 - bobs MB (var 3) * bobs MB (var 3)) * T
        + bobs MB (var 3) * (bobs MB (var 3) * T) := by noncomm_ring
    have hlast : snorm (dst ψ) (bOp (bobs MB (var 3) * (bobs MB (var 3) * T))
        : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) ≤ 24 * γ := by
      rw [bOp_mul]
      refine le_trans (snorm_mul_le (dst ψ) (bnd_bobs (dA := dA) (MB := MB) (var 3)) _) ?_
      rw [one_mul]
      exact hA
    rw [hsplit, bOp_add]
    refine le_trans (snorm_add_le _ _ _) ?_
    linarith
  -- step D: remove the trailing `b`
  have hD2 := hγ (con 4) 0
  rw [c40] at hD2
  have hiso := alice_isometry (dB := dB) D (con 4) 0
  have hcomm : (aOp (refl D (con 4) 0) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      * bOp (anti MB) = bOp (anti MB) * aOp (refl D (con 4) 0) := aOp_mul_bOp _ _
  have hrewrite : snorm (dst ψ) (bOp (anti MB) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = snorm (dst ψ) (bOp (anti MB) * aOp (refl D (con 4) 0)) := by
    rw [← hcomm, snorm_mul_of_isometry (dst ψ) hiso]
  have hsplit : (bOp (anti MB) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      * aOp (refl D (con 4) 0)
      = bOp T + bOp (anti MB) * (aOp (refl D (con 4) 0) - bOp (bobs MB (var 1))) := by
    rw [mul_sub, hT, bOp_mul]
    abel
  rw [hrewrite, hsplit]
  refine le_trans (snorm_add_le _ _ _) ?_
  have hlast := snorm_mul_le (dst ψ) (bnd_anti (dA := dA) (MB := MB))
    ((aOp (refl D (con 4) 0) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      - bOp (bobs MB (var 1)))
  linarith
end MIPRE.QLD.MS
