-- Prove2me | solution 1 for MIPRE.Introspection.fine_commutator_parseval
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:38:31.646802+00:00
-- url     : https://prove2.me/submissions/63dba537-2700-4631-9e2f-de6d8c87c97d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/PauliTwirlDistance.lean (solution of MIPRE.Introspection.fine_commutator_parseval);
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
import Theorems.Thm_MIPRE_Introspection_linear_measurement_fourier
import Theorems.Thm_MIPRE_Introspection_sum_norm_linearFourier_sq

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem mem_perp {S : Submodule F (Fin n → F)} {x : Fin n → F} :
    x ∈ perp S ↔ ∀ y ∈ S, ∑ i, y i * x i = 0 := by
  simp [perp, LinearMap.BilinForm.mem_orthogonal_iff]
end
end MIPRE.CL

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
theorem synOf_eq_zero_of_not_mem_range
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (a : Fin n → F) (ha : a ∉ L.range) :
    synOf w L a = 0 := by
  apply Finset.sum_eq_zero
  intro e he
  exact (ha ⟨e, (Finset.mem_filter.mp he).2⟩).elim
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Matrix Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]
/-- The readout/observable Parseval identity after any linear action on vectors. -/
theorem linear_measurement_parseval
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (f : Matrix (Fin n → F) (Fin n → F) ℂ →ₗ[ℂ] (N → ℂ)) :
    (∑ y : Fin n → F, ‖evec (f (synOf w L y))‖ ^ 2) =
      (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
        (∑ v : CL.perp L.ker, ‖evec (f (w v.1))‖ ^ 2) := by
  have h := sum_norm_linearFourier_sq L (fun y => f (synOf w L y))
    (fun y hy => by rw [synOf_eq_zero_of_not_mem_range w L y hy, map_zero])
  have hv (v : CL.perp L.ker) : f (w v.1) =
      ∑ y : Fin n → F, sgn (trDot v.1 (linearPreimage L y)) • f (synOf w L y) := by
    rw [linear_measurement_fourier w L v.1 v.2, map_sum]
    simp only [map_smul]
  simpa only [hv] using h.symm
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Matrix Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]
variable {H B : Type*} [Fintype H] [DecidableEq H] [Fintype B] [DecidableEq B]
/-- `lem:W`: the two commutator errors agree exactly, without a dimension factor. -/
theorem linear_measurement_commutator_parseval
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (ψ : ((Fin n → F) × H) × B → ℂ)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (∑ y : Fin n → F, stateSqNorm ψ
      (M * aOp (synOf w L y) - aOp (synOf w L y) * M)) =
    (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
      ∑ v : CL.perp L.ker, stateSqNorm ψ (M * aOp (w v.1) - aOp (w v.1) * M) :=
  linear_measurement_parseval w L (commutatorAction ψ M)
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Matrix Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
  {n : ℕ} {H K A : Type*} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype A]
theorem _root_.solution
    (ψ : ((Fin n → F) × H) × K → ℂ)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (∑ y : Fin n → F, stateSqNorm ψ
      (M * aOp (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) -
        aOp (synOf wZ (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)) y) * M)) =
    (Fintype.card (Fin n → F) : ℝ)⁻¹ * ∑ v : Fin n → F,
      stateSqNorm ψ (M * aOp (wZ v) - aOp (wZ v) * M) := by
  have h := linear_measurement_commutator_parseval wZ LinearMap.id ψ M
  have htop : CL.perp (LinearMap.id : (Fin n → F) →ₗ[F] (Fin n → F)).ker = ⊤ := by
    ext x
    simp [CL.mem_perp]
  rw [htop] at h
  have hc : Fintype.card (⊤ : Submodule F (Fin n → F)) = Fintype.card (Fin n → F) :=
    Fintype.card_congr (Submodule.topEquiv : (⊤ : Submodule F (Fin n → F)) ≃ₗ[F] _).toEquiv
  rw [hc] at h
  refine h.trans (congrArg (fun r : ℝ => (Fintype.card (Fin n → F) : ℝ)⁻¹ * r) ?_)
  exact Fintype.sum_equiv (Submodule.topEquiv : (⊤ : Submodule F (Fin n → F)) ≃ₗ[F] _).toEquiv
    _ _ (fun _ => rfl)
end MIPRE.Introspection
