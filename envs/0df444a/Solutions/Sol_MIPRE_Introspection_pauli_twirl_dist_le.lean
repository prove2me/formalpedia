-- Prove2me | solution 1 for MIPRE.Introspection.pauli_twirl_dist_le
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:46:22.940662+00:00
-- url     : https://prove2.me/submissions/f2f7705a-c55a-4bed-94fb-1a7b117a50e2

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PauliTwirlDistance.lean (solution of MIPRE.Introspection.pauli_twirl_dist_le);
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
import Definitions.Def_MIPRE_Foundations_Expanded
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Theorems.Thm_MIPRE_Introspection_composed_twirl_dist_le
import Theorems.Thm_MIPRE_Weyl_stateVec_epr
import Theorems.Thm_MIPRE_aOp_conjTranspose
import Theorems.Thm_MIPRE_aOp_mul
import Theorems.Thm_MIPRE_mulVec_kron_kron_expVec

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
/-- An isometry on the first factor is an isometry on the product space. -/
theorem isometry_aOp {X : Matrix HA HA ℂ} (h : Xᴴ * X = 1) :
    ((aOp X : Matrix (HA × HB) _ ℂ))ᴴ * aOp X = 1 := by
  rw [aOp_conjTranspose, ← aOp_mul, h, aOp_one]
end
end MIPRE

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix MIPRE
open scoped Kronecker
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- **The two parties' `X`-type operators act identically on the maximally entangled state.** -/
theorem stateVec_epr_wX (a : n → F) :
    stateVec (epr (F := F) (n := n)) (wX a) = stateVecB epr (wX a) := by
  rw [stateVec_epr, wX_transpose]
end
end MIPRE.Weyl

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl
open scoped Kronecker
variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
/-- Exact consistency survives adjoining any bipartite ancillary state. -/
theorem mirror_expVec (ψ : V × W → ℂ) (ξ : H × K → ℂ)
    (P : Matrix V V ℂ) (Q : Matrix W W ℂ) (h : stateVec ψ P = stateVecB ψ Q) :
    stateVec (expVec ψ ξ) (aOp P : Matrix (V × H) _ ℂ) =
      stateVecB (expVec ψ ξ) (aOp Q : Matrix (W × K) _ ℂ) := by
  have hbase := congrArg WithLp.ofLp h
  change (P ⊗ₖ (1 : Matrix W W ℂ)) *ᵥ ψ = ((1 : Matrix V V ℂ) ⊗ₖ Q) *ᵥ ψ at hbase
  unfold stateVec stateVecB aOp
  congr 1
  rw [show (1 : Matrix (W × K) (W × K) ℂ) =
      (1 : Matrix W W ℂ) ⊗ₖ (1 : Matrix K K ℂ) from Matrix.one_kronecker_one.symm,
    show (1 : Matrix (V × H) (V × H) ℂ) =
      (1 : Matrix V V ℂ) ⊗ₖ (1 : Matrix H H ℂ) from Matrix.one_kronecker_one.symm,
    mulVec_kron_kron_expVec, mulVec_kron_kron_expVec, hbase]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl
open scoped Kronecker
variable {V W H K : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F] {n : ℕ}
/-- The same `X` Pauli on the two EPR halves is an exact mirror, with arbitrary ancillas. -/
theorem eprWithAux_wX_mirror (ξ : H × K → ℂ) (v : Fin n → F) :
    xSqNorm (eprWithAux ξ) (aOp (wX v) : Matrix ((Fin n → F) × H) _ ℂ)
      (aOp (wX v) : Matrix ((Fin n → F) × K) _ ℂ) = 0 := by
  rw [xSqNorm, eprWithAux, mirror_expVec _ ξ _ _ (stateVec_epr_wX v), sub_self, norm_zero,
    zero_pow (by decide : 2 ≠ 0)]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype A]
/-- The concrete `Z` dephasing is the uniform unitary twirl. -/
theorem dephaseZ_eq_unitaryTwirl
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    dephaseZ M = unitaryTwirl (fun _ : Fin n → F => (Fintype.card (Fin n → F) : ℝ)⁻¹)
      (fun v => aOp (wZ v)) M := by
  simp only [dephaseZ, unitaryTwirl, amplify, ← Finset.smul_sum,
    aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, wZ_conjTranspose,
    Complex.ofReal_inv, Complex.ofReal_natCast]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype A]
/-- The concrete kernel averaging is the uniform `X` twirl. -/
theorem averageX_eq_unitaryTwirl (S : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    averageX S M = unitaryTwirl (fun _ : S => (Fintype.card S : ℝ)⁻¹)
      (fun v => aOp (wX v.1)) M := by
  simp only [averageX, unitaryTwirl, amplify, ← Finset.smul_sum,
    aOp, Matrix.conjTranspose_kronecker, Matrix.conjTranspose_one, wX_conjTranspose,
    Complex.ofReal_inv, Complex.ofReal_natCast]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype A]
theorem _root_.solution (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ξ : H × K → ℂ) (M : POVM A ((Fin n → F) × H)) :
    (∑ a, stateSqNorm (eprWithAux ξ)
      (averageX L.ker (dephaseZ (M.mats a).val) - (M.mats a).val)) ≤
      4 * ((Fintype.card (Fin n → F) : ℝ)⁻¹ * ∑ v : Fin n → F, ∑ a,
        stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wZ v) - aOp (wZ v) * (M.mats a).val)) +
      4 * ((Fintype.card L.ker : ℝ)⁻¹ * ∑ v : L.ker, ∑ a,
        stateSqNorm (eprWithAux ξ) ((M.mats a).val * aOp (wX v.1) - aOp (wX v.1) * (M.mats a).val)) := by
  have h := composed_twirl_dist_le
    (fun _ : Fin n → F => (Fintype.card (Fin n → F) : ℝ)⁻¹)
    (fun _ : L.ker => (Fintype.card L.ker : ℝ)⁻¹)
    (by intros; positivity) (by intros; positivity)
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero))
    (by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)) (eprWithAux ξ) M
    (fun v => aOp (wZ v)) (fun v : L.ker => aOp (wX v.1))
    (fun v : L.ker => (aOp (wX v.1) : Matrix ((Fin n → F) × K) _ ℂ))
    (fun v => by rw [aOp_conjTranspose, wZ_conjTranspose])
    (fun v => by rw [← aOp_mul, wZ_mul_self, aOp_one])
    (fun v => by rw [aOp_conjTranspose, wX_conjTranspose])
    (fun v => by rw [← aOp_mul, wX_mul_self, aOp_one])
    (fun v => isometry_aOp (by rw [wX_conjTranspose, wX_mul_self]))
    (fun v => eprWithAux_wX_mirror ξ v.1)
  simpa only [← dephaseZ_eq_unitaryTwirl, ← averageX_eq_unitaryTwirl, ← Finset.mul_sum] using h
end MIPRE.Introspection
