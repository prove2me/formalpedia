-- Prove2me | solution 1 for MIPRE.QLD.MS.path
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:38:53.110979+00:00
-- url     : https://prove2.me/submissions/900e3457-4ac3-4701-9b0d-b0e84bee100c

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (solution of MIPRE.QLD.MS.path);
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
import Theorems.Thm_MIPRE_QLD_MS_dd_suffix
import Theorems.Thm_MIPRE_QLD_MS_relation_core
import Theorems.Thm_MIPRE_QLD_MS_word2
import Theorems.Thm_MIPRE_bnd_one_of_conjTranspose_mul_self_le
import Theorems.Thm_MIPRE_pvmObs_mul
import Theorems.Thm_MIPRE_sgn_add
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
theorem snorm_smul (c : ℂ) (M : Matrix N N ℂ) : snorm v (c • M) = ‖c‖ * snorm v M := by
  rw [snorm, snorm, Matrix.smul_mulVec, evec_smul, norm_smul]
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

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
/-- Two weightings of the *same* measurement commute. -/
theorem pvmObs_comm (h : IsPVM P) (ε δ : Λ → ℂ) :
    pvmObs P ε * pvmObs P δ = pvmObs P δ * pvmObs P ε := by
  rw [pvmObs_mul h, pvmObs_mul h, mul_comm]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {n Λ : Type*} [Fintype n] [DecidableEq n] [Fintype Λ] [DecidableEq Λ]
variable {P : Λ → Matrix n n ℂ}
/-- Three weightings whose pointwise product is the constant `s` multiply to `s • 1`
**exactly**. -/
theorem pvmObs_mul_mul (h : IsPVM P) {ε δ η : Λ → ℂ} {s : ℂ}
    (hs : ∀ a, ε a * δ a * η a = s) :
    pvmObs P ε * pvmObs P δ * pvmObs P η = s • (1 : Matrix n n ℂ) := by
  rw [pvmObs_mul h, pvmObs_mul h]
  rw [show ε * δ * η = fun _ => s from funext fun a => hs a]
  exact pvmObs_const h s
end
end MIPRE

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
theorem pvBit_sum (c : Fin layout.r) (k : PV) :
    pvBit c k 0 + pvBit c k 1 + pvBit c k 2 = game.b c := by
  revert c k
  decide
end
end MIPRE.QLD.MS

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
/-- **The three signs of a constraint multiply to its sign.** -/
theorem csgn_prod (c : Fin layout.r) (k : PV) :
    csgn c 0 k * csgn c 1 k * csgn c 2 k = sgn (game.b c) := by
  rw [csgn, csgn, csgn, ← sgn_add, ← sgn_add, pvBit_sum]
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
theorem refl_comm (D : Dilated MA) (c : Fin layout.r) (i j : Fin 3) :
    refl D c i * refl D c j = refl D c j * refl D c i :=
  pvmObs_comm (D.isPVM c) _ _
end
end MIPRE.QLD.MS

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
/-- **The three reflections of a constraint multiply to its sign, exactly.** -/
theorem refl_prod (D : Dilated MA) (c : Fin layout.r) :
    refl D c 0 * refl D c 1 * refl D c 2 = sgn (game.b c) • 1 :=
  pvmObs_mul_mul (D.isPVM c) fun k => csgn_prod c k
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
/-- **The three reflections of a constraint, in the form the relations use**: the product of the
first two is the constraint's sign times the third. -/
theorem refl_two_eq (D : Dilated MA) (c : Fin layout.r) :
    refl D c 0 * refl D c 1 = sgn (game.b c) • refl D c 2 := by
  have h := refl_prod D c
  calc refl D c 0 * refl D c 1 = refl D c 0 * refl D c 1 * refl D c 2 * refl D c 2 := by
        rw [mul_assoc (refl D c 0 * refl D c 1), refl_mul_self, mul_one]
    _ = (sgn (game.b c) • (1 : Matrix (dA × PV) (dA × PV) ℂ)) * refl D c 2 := by rw [h]
    _ = sgn (game.b c) • refl D c 2 := by rw [Matrix.smul_mul, Matrix.one_mul]
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
theorem dd_comm (ψ : dA × dB → ℂ) (X Y : Matrix dB dB ℂ) : dd ψ X Y = dd ψ Y X :=
  snorm_sub_comm _ _ _
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
theorem dd_triangle (ψ : dA × dB → ℂ) (X Y Z : Matrix dB dB ℂ) :
    dd ψ X Z ≤ dd ψ X Y + dd ψ Y Z := by
  have h : (bOp X - bOp Z : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = (bOp X - bOp Y) + (bOp Y - bOp Z) := by abel
  rw [dd, h]
  exact snorm_add_le _ _ _
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
/-- Negating both sides changes nothing. -/
theorem dd_neg (ψ : dA × dB → ℂ) (X Y : Matrix dB dB ℂ) : dd ψ (-X) (-Y) = dd ψ X Y := by
  have h : (bOp (-X) - bOp (-Y) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = (-1 : ℂ) • (bOp X - bOp Y) := by
    rw [show (-X) = (-1 : ℂ) • X from by module, show (-Y) = (-1 : ℂ) • Y from by module,
      bOp_smul, bOp_smul]
    module
  rw [dd, dd, h, snorm_smul]
  norm_num
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
/-- A Bob prefix does not increase the distance. -/
theorem dd_prefix {P : Matrix dB dB ℂ}
    (hP : Bnd (bOp P : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1) (X Y : Matrix dB dB ℂ) :
    dd ψ (P * X) (P * Y) ≤ dd ψ X Y := by
  have h : (bOp (P * X) - bOp (P * Y) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
      = bOp P * (bOp X - bOp Y) := by rw [bOp_mul, bOp_mul, mul_sub]
  rw [dd, h]
  have := snorm_mul_le (dst ψ) hP (bOp X - bOp Y : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ)
  rw [one_mul] at this
  exact this
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
theorem relation10
    (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c : Fin layout.r) :
    dd ψ (bobs MB (cell c 1) * bobs MB (cell c 0)) (sgn (game.b c) • bobs MB (cell c 2))
      ≤ 3 * γ :=
  relation_core hγ c 1 0 (refl_two_eq D c)
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
theorem relation01
    (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ)
    (c : Fin layout.r) :
    dd ψ (bobs MB (cell c 0) * bobs MB (cell c 1)) (sgn (game.b c) • bobs MB (cell c 2))
      ≤ 3 * γ :=
  relation_core hγ c 0 1 (by rw [refl_comm]; exact refl_two_eq D c)
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
theorem _root_.solution (hγ : ∀ c j, snorm (dst ψ) (aOp (refl D c j) - bOp (bobs MB (cell c j))) ≤ γ) :
    dd ψ (bobs MB (var 3) * bobs MB (var 0) * (bobs MB (var 4) * bobs MB (var 1)))
      (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1)))) ≤ 24 * γ := by
  have c00 : cell (con 0) 0 = var 0 := rfl
  have c01 : cell (con 0) 1 = var 1 := rfl
  have c02 : cell (con 0) 2 = var 2 := rfl
  have c10 : cell (con 1) 0 = var 3 := rfl
  have c11 : cell (con 1) 1 = var 4 := rfl
  have c12 : cell (con 1) 2 = var 5 := rfl
  have c20 : cell (con 2) 0 = var 6 := rfl
  have c21 : cell (con 2) 1 = var 7 := rfl
  have c22 : cell (con 2) 2 = var 8 := rfl
  have c30 : cell (con 3) 0 = var 0 := rfl
  have c31 : cell (con 3) 1 = var 3 := rfl
  have c32 : cell (con 3) 2 = var 6 := rfl
  have c40 : cell (con 4) 0 = var 1 := rfl
  have c41 : cell (con 4) 1 = var 4 := rfl
  have c42 : cell (con 4) 2 = var 7 := rfl
  have c50 : cell (con 5) 0 = var 2 := rfl
  have c51 : cell (con 5) 1 = var 5 := rfl
  have c52 : cell (con 5) 2 = var 8 := rfl
  have hb0 : game.b (con 0) = 0 := by decide
  have hb1 : game.b (con 1) = 0 := by decide
  have hb2 : game.b (con 2) = 0 := by decide
  have hb3 : game.b (con 3) = 0 := by decide
  have hb4 : game.b (con 4) = 0 := by decide
  have hb5 : game.b (con 5) = 1 := by decide
  have hb34 : Bnd (bOp (bobs MB (var 3) * bobs MB (var 4)) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 :=
    bnd_bobs_mul (dA := dA) _ _ (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  have hb30 : Bnd (bOp (bobs MB (var 3) * bobs MB (var 0)) : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) 1 :=
    bnd_bobs_mul (dA := dA) _ _ (bnd_bobs (dA := dA) (MB := MB) _) (bnd_bobs (dA := dA) (MB := MB) _)
  -- the six within-constraint relations
  have r3 : dd ψ (bobs MB (var 3) * bobs MB (var 0)) (bobs MB (var 6)) ≤ 3 * γ := by
    have h := relation10 hγ (con 3)
    rw [c31, c30, c32, hb3, sgn_zero, one_smul] at h
    exact h
  have r4 : dd ψ (bobs MB (var 4) * bobs MB (var 1)) (bobs MB (var 7)) ≤ 3 * γ := by
    have h := relation10 hγ (con 4)
    rw [c41, c40, c42, hb4, sgn_zero, one_smul] at h
    exact h
  have r2 : dd ψ (bobs MB (var 6) * bobs MB (var 7)) (bobs MB (var 8)) ≤ 3 * γ := by
    have h := relation01 hγ (con 2)
    rw [c20, c21, c22, hb2, sgn_zero, one_smul] at h
    exact h
  have r5 : dd ψ (bobs MB (var 5) * bobs MB (var 2)) (-bobs MB (var 8)) ≤ 3 * γ := by
    have h := relation10 hγ (con 5)
    rw [c51, c50, c52, hb5, sgn_one, neg_one_smul] at h
    exact h
  have r1 : dd ψ (bobs MB (var 5)) (bobs MB (var 3) * bobs MB (var 4)) ≤ 3 * γ := by
    have h := relation01 hγ (con 1)
    rw [c10, c11, c12, hb1, sgn_zero, one_smul] at h
    rw [dd_comm]
    exact h
  have r0 : dd ψ (bobs MB (var 2)) (bobs MB (var 0) * bobs MB (var 1)) ≤ 3 * γ := by
    have h := relation01 hγ (con 0)
    rw [c00, c01, c02, hb0, sgn_zero, one_smul] at h
    rw [dd_comm]
    exact h
  -- step 1: `d a e b` to `g e b`, with the suffix `e b`
  have s1 : dd ψ (bobs MB (var 3) * bobs MB (var 0) * (bobs MB (var 4) * bobs MB (var 1))) (bobs MB (var 6) * (bobs MB (var 4) * bobs MB (var 1))) ≤ 7 * γ := by
    have hsuf := word2 hγ (con 4) (con 4) 1 0
    rw [c41, c40] at hsuf
    have h := dd_suffix (ψ := ψ) (X := bobs MB (var 3) * bobs MB (var 0)) (Y := bobs MB (var 6)) (W := bobs MB (var 4) * bobs MB (var 1))
      hb30 (bnd_bobs (dA := dA) (MB := MB) _)
      (isometry_mul (refl_isometry D (con 4) 0) (refl_isometry D (con 4) 1)) hsuf
    linarith
  -- step 2: `g e b` to `g h`, behind the prefix `g`
  have s2 : dd ψ (bobs MB (var 6) * (bobs MB (var 4) * bobs MB (var 1))) (bobs MB (var 6) * bobs MB (var 7)) ≤ 3 * γ := by
    have h := dd_prefix (ψ := ψ) (P := bobs MB (var 6)) (bnd_bobs (dA := dA) (MB := MB) _) (bobs MB (var 4) * bobs MB (var 1)) (bobs MB (var 7))
    linarith
  -- step 3: `g h` to `i`
  have s3 : dd ψ (bobs MB (var 6) * bobs MB (var 7)) (bobs MB (var 8)) ≤ 3 * γ := r2
  -- step 4: `i` to `- f c`, the one constraint of product `-1`
  have s4 : dd ψ (bobs MB (var 8)) (-(bobs MB (var 5) * bobs MB (var 2))) ≤ 3 * γ := by
    rw [dd_comm]
    have h := dd_neg ψ (bobs MB (var 5) * bobs MB (var 2)) (-bobs MB (var 8))
    rw [neg_neg] at h
    rw [h]
    exact r5
  -- step 5: `- f c` to `- d e c`, with the suffix `c`
  have s5 : dd ψ (-(bobs MB (var 5) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * bobs MB (var 2))) ≤ 5 * γ := by
    have hw := word1 hγ (con 0) 2
    rw [c02] at hw
    have h := dd_suffix (ψ := ψ) (X := bobs MB (var 5)) (Y := bobs MB (var 3) * bobs MB (var 4)) (W := bobs MB (var 2))
      (bnd_bobs (dA := dA) (MB := MB) _) hb34 (refl_isometry D (con 0) 2) hw
    rw [dd_neg]
    linarith
  -- step 6: `- d e c` to `- d e a b`, behind the prefix `d e`
  have s6 : dd ψ (-(bobs MB (var 3) * bobs MB (var 4) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1)))) ≤ 3 * γ := by
    have h := dd_prefix (ψ := ψ) (P := bobs MB (var 3) * bobs MB (var 4)) hb34 (bobs MB (var 2)) (bobs MB (var 0) * bobs MB (var 1))
    rw [dd_neg]
    linarith
  -- chain the six steps
  have t1 := dd_triangle ψ (bobs MB (var 3) * bobs MB (var 0) * (bobs MB (var 4) * bobs MB (var 1))) (bobs MB (var 6) * (bobs MB (var 4) * bobs MB (var 1))) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  have t2 := dd_triangle ψ (bobs MB (var 6) * (bobs MB (var 4) * bobs MB (var 1))) (bobs MB (var 6) * bobs MB (var 7)) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  have t3 := dd_triangle ψ (bobs MB (var 6) * bobs MB (var 7)) (bobs MB (var 8)) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  have t4 := dd_triangle ψ (bobs MB (var 8)) (-(bobs MB (var 5) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  have t5 := dd_triangle ψ (-(bobs MB (var 5) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * bobs MB (var 2))) (-(bobs MB (var 3) * bobs MB (var 4) * (bobs MB (var 0) * bobs MB (var 1))))
  linarith
end MIPRE.QLD.MS
