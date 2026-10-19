-- Prove2me | solution 1 for MIPRE.sum_snorm_sq_chain
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T01:44:19.5392+00:00
-- url     : https://prove2.me/submissions/966e9533-7ec5-4db5-863f-c82a51f82d40

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/OracularTensor.lean (solution of MIPRE.sum_snorm_sq_chain);
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
import Definitions.Def_MIPRE_Foundations_OracularGame
import Definitions.Def_MIPRE_Foundations_Closeness
import Definitions.Def_MIPRE_Foundations_PerfectStrategy
import Definitions.Def_MIPRE_Foundations_GameTransport
import Definitions.Def_MIPRE_Foundations_GameDouble
import Definitions.Def_MIPRE_Foundations_OracularSound
import Definitions.Def_MIPRE_Foundations_OpBound
import Definitions.Def_MIPRE_Foundations_StateDistance
import Definitions.Def_MIPRE_Foundations_POVMValue
import Definitions.Def_MIPRE_Foundations_CrossConsistency
import Definitions.Def_MIPRE_Foundations_PVM
import Definitions.Def_MIPRE_Foundations_Commutation
import Definitions.Def_MIPRE_Foundations_Dilation
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_Sandwich
import Definitions.Def_MIPRE_Foundations_POVMMix
import Definitions.Def_MIPRE_Foundations_GameAdapt
import Definitions.Def_MIPRE_Foundations_RegisterReindex
import Definitions.Def_MIPRE_Foundations_OracularTensor
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_sum
import Theorems.Thm_MIPRE_sum_snorm_sq_mul_le
import Theorems.Thm_MIPRE_sum_snorm_sq_triangle3

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
theorem snorm_sub_comm (M M' : Matrix N N ℂ) : snorm v (M - M') = snorm v (M' - M) := by
  rw [snorm, snorm, Matrix.sub_mulVec, Matrix.sub_mulVec, evec_sub, evec_sub, norm_sub_rev]
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
theorem aOp_mul (X Y : Matrix HA HA ℂ) :
    aOp (X * Y) = (aOp X : Matrix (HA × HB) _ ℂ) * aOp Y := by
  rw [aOp, aOp, aOp, ← Matrix.mul_kronecker_mul, Matrix.one_mul]
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
open scoped ComplexOrder MatrixOrder
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
/-- A projective family on Bob's factor satisfies the hypothesis of `sum_snorm_sq_mul_le` with
equality. -/
theorem sum_bOp_conjTranspose_mul_self_of_isPVM {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Q : ι → Matrix dB dB ℂ} (h : IsPVM Q) :
    ∑ i, ((bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * bOp (Q i)
      = (1 : Matrix (dA × dB) (dA × dB) ℂ) := by
  have hterm : ∀ i : ι, ((bOp (Q i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * bOp (Q i)
      = bOp (Q i) := by
    intro i
    rw [bOp_conjTranspose, ← bOp_mul, h.isSelfAdjoint, h.idem]
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← bOp_sum, h.sum_eq_one, bOp_one]
end
end MIPRE

namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
variable {dA dB : Type*} [Fintype dA] [DecidableEq dA] [Fintype dB] [DecidableEq dB]
theorem sum_aOp_conjTranspose_mul_self_of_isPVM {ι : Type*} [Fintype ι]
    {P : ι → Matrix dA dA ℂ} (h : IsPVM P) :
    ∑ i, ((aOp (P i) : Matrix (dA × dB) (dA × dB) ℂ))ᴴ * aOp (P i) = 1 := by
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => by
      rw [aOp_conjTranspose, h.isSelfAdjoint, ← aOp_mul, h.idem],
    ← aOp_sum, h.sum_eq_one, aOp_one]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Finset Matrix
open scoped ComplexOrder MatrixOrder
variable {HA HB : Type*} [Fintype HA] [DecidableEq HA] [Fintype HB] [DecidableEq HB]
theorem _root_.solution (ψ : HA × HB → ℂ) {K : Type*} [Fintype K] [DecidableEq K]
    (C OA OB : K → Matrix HA HA ℂ) (P Q : K → Matrix HB HB ℂ) (hQ : IsPVM Q) (hOA : IsPVM OA) :
    ∑ o : K × K,
        snorm ψ ((aOp (C o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2)
          - aOp (OA o.1 * OB o.2)) ^ 2
      ≤ 3 * ∑ u, snorm ψ ((aOp (C u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
        + 3 * ∑ u, snorm ψ ((aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2
        + 3 * ∑ v, snorm ψ ((aOp (OB v) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (Q v)) ^ 2 := by
  have hQF : ∑ v, ((bOp (Q v) : Matrix (HA × HB) (HA × HB) ℂ))ᴴ * bOp (Q v)
      ≤ (1 : Matrix (HA × HB) (HA × HB) ℂ) :=
    le_of_eq (sum_bOp_conjTranspose_mul_self_of_isPVM hQ)
  have hOF : ∑ u, ((aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ))ᴴ * aOp (OA u)
      ≤ (1 : Matrix (HA × HB) (HA × HB) ℂ) :=
    le_of_eq (sum_aOp_conjTranspose_mul_self_of_isPVM hOA)
  refine le_trans (sum_snorm_sq_triangle3 ψ
    (fun o : K × K => (aOp (C o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2))
    (fun o => (bOp (Q o.2) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (P o.1))
    (fun o => (aOp (OA o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2))
    (fun o => (aOp (OA o.1 * OB o.2) : Matrix (HA × HB) (HA × HB) ℂ))) ?_
  -- the first deviation: `(Id ⊗ Q_v)(C_u ⊗ Id - Id ⊗ P_u)`
  have h1 : ∑ o : K × K, snorm ψ ((aOp (C o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2)
        - bOp (Q o.2) * bOp (P o.1)) ^ 2
      ≤ ∑ u, snorm ψ ((aOp (C u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun u _ => ?_
    have heq : ∀ v, (aOp (C u) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q v)
        - bOp (Q v) * bOp (P u) = bOp (Q v) * (aOp (C u) - bOp (P u)) := fun v => by
      rw [aOp_mul_bOp, Matrix.mul_sub]
    simp only [heq]
    exact sum_snorm_sq_mul_le ψ (fun v => (bOp (Q v) : Matrix (HA × HB) (HA × HB) ℂ)) hQF _
  -- the second: `(Id ⊗ Q_v)(Id ⊗ P_u - O^𝖠_u ⊗ Id)`
  have h2 : ∑ o : K × K, snorm ψ ((bOp (Q o.2) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (P o.1)
        - aOp (OA o.1) * bOp (Q o.2)) ^ 2
      ≤ ∑ u, snorm ψ ((aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (P u)) ^ 2 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_le_sum fun u _ => ?_
    have heq : ∀ v, (bOp (Q v) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (P u)
        - aOp (OA u) * bOp (Q v) = bOp (Q v) * (bOp (P u) - aOp (OA u)) := fun v => by
      rw [aOp_mul_bOp, Matrix.mul_sub]
    simp only [heq]
    rw [snorm_sub_comm]
    exact sum_snorm_sq_mul_le ψ (fun v => (bOp (Q v) : Matrix (HA × HB) (HA × HB) ℂ)) hQF _
  -- the third: `(O^𝖠_u ⊗ Id)(Id ⊗ Q_v - O^𝖡_v ⊗ Id)`
  have h3 : ∑ o : K × K, snorm ψ ((aOp (OA o.1) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q o.2)
        - aOp (OA o.1 * OB o.2)) ^ 2
      ≤ ∑ v, snorm ψ ((aOp (OB v) : Matrix (HA × HB) (HA × HB) ℂ) - bOp (Q v)) ^ 2 := by
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_le_sum fun v _ => ?_
    have heq : ∀ u, (aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ) * bOp (Q v)
        - aOp (OA u * OB v) = aOp (OA u) * (bOp (Q v) - aOp (OB v)) := fun u => by
      rw [aOp_mul, Matrix.mul_sub]
    simp only [heq]
    rw [snorm_sub_comm]
    exact sum_snorm_sq_mul_le ψ (fun u => (aOp (OA u) : Matrix (HA × HB) (HA × HB) ℂ)) hOF _
  linarith
end MIPRE
