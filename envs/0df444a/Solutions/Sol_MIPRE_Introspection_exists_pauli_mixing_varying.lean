-- Prove2me | solution 1 for MIPRE.Introspection.exists_pauli_mixing_varying
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:49:47.339065+00:00
-- url     : https://prove2.me/submissions/1768a7bc-7e75-4a97-8189-42ed2e9b223b

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/VaryingPauliMixing.lean (solution of MIPRE.Introspection.exists_pauli_mixing_varying);
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
import Definitions.Def_MIPRE_Foundations_WeylEPR
import Definitions.Def_MIPRE_Foundations_Introspection_TwirlDistance
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Definitions.Def_MIPRE_Foundations_Introspection_BlockPOVM
import Definitions.Def_MIPRE_Foundations_Introspection_EPR
import Definitions.Def_MIPRE_Foundations_Introspection_BlockRetention
import Definitions.Def_MIPRE_Foundations_Introspection_PauliMixing
import Theorems.Thm_MIPRE_Introspection_exists_pauli_mixing
import Theorems.Thm_MIPRE_sum_weighted_mul_le_sqrt

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
noncomputable section
open Finset Matrix
open scoped ComplexOrder MatrixOrder Kronecker
set_option linter.unusedSectionVars false
/-- **Moving an average inside a square root.** Cauchy--Schwarz against the constant one. -/
theorem sum_weighted_sqrt_le {ι : Type*} [Fintype ι] (w f : ι → ℝ) (hw0 : ∀ i, 0 ≤ w i)
    (hw1 : ∑ i, w i = 1) (hf : ∀ i, 0 ≤ f i) :
    ∑ i, w i * Real.sqrt (f i) ≤ Real.sqrt (∑ i, w i * f i) := by
  have h := sum_weighted_mul_le_sqrt w (fun i => Real.sqrt (f i)) (fun _ => (1 : ℝ)) hw0
  rw [Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * (Real.sqrt (f i) * 1) = w i * Real.sqrt (f i) from by rw [mul_one],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show
      w i * Real.sqrt (f i) ^ 2 = w i * f i from by rw [Real.sq_sqrt (hf i)],
    Finset.sum_congr rfl fun i (_ : i ∈ univ) => show w i * (1 : ℝ) ^ 2 = w i from by ring,
    hw1, Real.sqrt_one, mul_one] at h
  exact h
end
end MIPRE

namespace MIPRE.Introspection
noncomputable section
open Finset Matrix Weyl Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype A] [DecidableEq A]
/-- Every term entering the mixing error is a squared norm. -/
theorem mixingError_nonneg (L : (Fin n → F) →ₗ[F] (Fin n → F)) (ξ : H × K → ℂ)
    (M : POVM ((Fin n → F) × A) ((Fin n → F) × H)) : 0 ≤ mixingError L ξ M := by
  unfold mixingError readoutMarginalError readoutCommutatorError stateSqNorm stateNorm
  positivity
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical
open scoped Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {X A : Type*} [Fintype X] [Fintype A] [DecidableEq A]
  {n : X → ℕ} {H K : X → Type*}
  [∀ x, Fintype (H x)] [∀ x, DecidableEq (H x)]
  [∀ x, Fintype (K x)] [∀ x, DecidableEq (K x)]
theorem _root_.solution
    (D : X → ℝ) (hD0 : ∀ x, 0 ≤ D x) (hD1 : ∑ x, D x = 1)
    (L : (x : X) → (Fin (n x) → F) →ₗ[F] (Fin (n x) → F))
    (ξ : (x : X) → H x × K x → ℂ) (hξ : ∀ x, ‖evec (ξ x)‖ = 1)
    (M : (x : X) → POVM ((Fin (n x) → F) × A) ((Fin (n x) → F) × H x))
    (hM : ∀ x, IsPVM (fun p => ((M x).mats p).val))
    {δ : ℝ} (hδ : ∑ x, D x * mixingError (L x) (ξ x) (M x) ≤ δ) :
    ∃ Q : (x : X) → (Fin (n x) → F) → POVM A (H x),
      (∑ x, D x * ∑ p : (Fin (n x) → F) × A, stateSqNorm (eprWithAux (ξ x))
        (((M x).mats p).val - synOf wZ (L x) p.1 ⊗ₖ ((Q x p.1).mats p.2).val)) ≤
      2 * δ + 4 * Real.sqrt δ := by
  choose Q hQ using fun x => exists_pauli_mixing (L x) (ξ x) (hξ x) (M x) (hM x)
  refine ⟨Q, ?_⟩
  have hsum := Finset.sum_le_sum fun x (_ : x ∈ univ) =>
    mul_le_mul_of_nonneg_left (hQ x) (hD0 x)
  have hroot := (sum_weighted_sqrt_le D (fun x => mixingError (L x) (ξ x) (M x)) hD0 hD1
    (fun x => mixingError_nonneg (L x) (ξ x) (M x))).trans (Real.sqrt_le_sqrt hδ)
  have heq : (∑ x, D x * (2 * mixingError (L x) (ξ x) (M x) +
      4 * Real.sqrt (mixingError (L x) (ξ x) (M x)))) =
      2 * (∑ x, D x * mixingError (L x) (ξ x) (M x)) +
      4 * ∑ x, D x * Real.sqrt (mixingError (L x) (ξ x) (M x)) := by
    simp only [mul_add, Finset.sum_add_distrib, mul_left_comm (b := (2 : ℝ)),
      mul_left_comm (b := (4 : ℝ)), ← Finset.mul_sum]
  rw [heq] at hsum
  linarith
end MIPRE.Introspection
