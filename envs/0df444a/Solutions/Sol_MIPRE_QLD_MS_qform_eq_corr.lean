-- Prove2me | solution 1 for MIPRE.QLD.MS.qform_eq_corr
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:30:22.992981+00:00
-- url     : https://prove2.me/submissions/8539024e-8faf-41d5-a4cd-4b670a7cb179

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/QLD/Anticomm.lean (solution of MIPRE.QLD.MS.qform_eq_corr);
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
import Theorems.Thm_MIPRE_QLD_MS_emb_compress_refl
import Theorems.Thm_MIPRE_sum_kronecker_left

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
theorem qform_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix N N ℂ) :
    qform v (∑ i ∈ s, f i) = ∑ i ∈ s, qform v (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [qform]
  | insert i s hi ih => rw [Finset.sum_insert hi, qform_add, ih, Finset.sum_insert hi]
end
end MIPRE

namespace MIPRE.QLD.MS
noncomputable section
open Finset Matrix Kronecker MIPRE MIPRE.LCS MIPRE.LCS.MagicSquare
open scoped ComplexOrder MatrixOrder
variable {dA dB : Type} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
variable {MA : layout.Question → POVM layout.Answer dA}
variable {MB : layout.Question → POVM layout.Answer dB}
variable {MA : layout.Question → POVM layout.Answer dA}
theorem sgn_eq_rsgn (x : ZMod 2) : sgn x = ((rsgn x : ℝ) : ℂ) := by
  rw [sgn, rsgn]; split_ifs <;> norm_num
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
theorem sum_zmod2 {M : Type*} [AddCommMonoid M] (f : ZMod 2 → M) :
    ∑ w : ZMod 2, f w = f 0 + f 1 := by
  show ∑ w : Fin 2, f w = f 0 + f 1
  exact Fin.sum_univ_two f
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
theorem aOp_mul_bOp_eq (X : Matrix (dA × PV) (dA × PV) ℂ) (Y : Matrix dB dB ℂ) :
    (aOp X : Matrix ((dA × PV) × dB) ((dA × PV) × dB) ℂ) * bOp Y = X ⊗ₖ Y := by
  rw [aOp, bOp, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
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
/-- The quadratic form on the dilated state compresses the Alice factor. -/
theorem qform_dst (X : Matrix (dA × PV) (dA × PV) ℂ) (Y : Matrix dB dB ℂ) :
    qform (dst ψ) (X ⊗ₖ Y) = qform ψ (((emb dA)ᴴ * (X * emb dA)) ⊗ₖ Y) := by
  have hmat : (((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ)))ᴴ
      * ((X ⊗ₖ Y) * ((emb dA) ⊗ₖ (1 : Matrix dB dB ℂ)))
      = ((emb dA)ᴴ * (X * emb dA)) ⊗ₖ Y := by
    rw [Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one,
      ← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul]
  rw [qform, qform, dst, Matrix.mulVec_mulVec, star_mulVec_dotProduct, hmat]
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
theorem _root_.solution (D : Dilated MA) (c : Fin layout.r) (j : Fin 3) :
    qform (dst ψ) (aOp (refl D c j) * bOp (bobs MB (cell c j))) = corr ψ MA MB c j := by
  classical
  rw [aOp_mul_bOp_eq, qform_dst, emb_compress_refl]
  -- expand the Alice sum
  rw [sum_kronecker_left, qform_sum]
  rw [corr]
  refine Finset.sum_congr rfl fun d _ => ?_
  -- pull out the sign
  rw [show (csgn c j (rep c d) • ((MA (Sum.inl c)).mats d).val) ⊗ₖ bobs MB (cell c j)
      = ((rsgn (pvBit c (rep c d) j) : ℝ) : ℂ)
        • (((MA (Sum.inl c)).mats d).val ⊗ₖ bobs MB (cell c j)) from by
    rw [Matrix.smul_kronecker, csgn, sgn_eq_rsgn], qform_smul_real]
  -- expand Bob's observable
  rw [sum_zmod2 (fun w => rsgn (pvBit c (rep c d) j) * rsgn w
    * bornProb ψ (((MA (Sum.inl c)).mats d).val)
        (((MB (Sum.inr (cell c j))).mats (Sum.inr w)).val))]
  rw [show (((MA (Sum.inl c)).mats d).val ⊗ₖ bobs MB (cell c j))
      = (((MA (Sum.inl c)).mats d).val ⊗ₖ ((MB (Sum.inr (cell c j))).mats (Sum.inr 0)).val)
        + (((-1 : ℝ) : ℂ)) • (((MA (Sum.inl c)).mats d).val
            ⊗ₖ ((MB (Sum.inr (cell c j))).mats (Sum.inr 1)).val) from by
    rw [← Matrix.kronecker_smul, ← Matrix.kronecker_add, bobs]
    congr 1
    module, qform_add, qform_smul_real]
  have h0 : rsgn (0 : ZMod 2) = 1 := by rw [rsgn]; norm_num
  have h1 : rsgn (1 : ZMod 2) = -1 := by rw [rsgn]; norm_num
  rw [h0, h1, bornProb, bornProb, qform, qform]
  ring
end MIPRE.QLD.MS
