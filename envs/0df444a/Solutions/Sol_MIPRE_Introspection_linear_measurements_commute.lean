-- Prove2me | solution 1 for MIPRE.Introspection.linear_measurements_commute
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:38:31.040859+00:00
-- url     : https://prove2.me/submissions/f131d118-06e1-400f-9fd9-3c565ef359bc

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/Commutation.lean (solution of MIPRE.Introspection.linear_measurements_commute);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Pi
import Mathlib.RingTheory.Trace.Basic
import Mathlib.Tactic.IntervalCases
import Definitions.Def_MIPRE_Foundations_CL_Register
import Definitions.Def_MIPRE_Foundations_CL_Canonical
import Definitions.Def_MIPRE_Foundations_LowDegree_Encoding
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Theorems.Thm_MIPRE_Introspection_linear_measurement_fourier_inverse
import Theorems.Thm_MIPRE_Weyl_wX_mul_wZ

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

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The commuting case. -/
theorem wX_mul_wZ_of_eq (a b : n → F) (h : trDot a b = 0) :
    wX a * wZ b = wZ b * wX a := by
  rw [wX_mul_wZ, h, sgn_zero, one_smul]
end
end MIPRE.Weyl

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
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
theorem commute_matrix_smul {ι : Type*} [Fintype ι]
    {A B : Matrix ι ι ℂ} (h : Commute A B) (c d : ℂ) : Commute (c • A) (d • B) := by
  change (c • A) * (d • B) = (d • B) * (c • A)
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  rw [h.eq, mul_comm c d]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
theorem _root_.solution
    (L R : (Fin n → F) →ₗ[F] (Fin n → F)) (hLR : CL.perp R.ker ≤ L.ker)
    (a b : Fin n → F) : Commute (synOf wZ L a) (synOf wX R b) := by
  by_cases ha : a ∈ L.range
  swap
  · rw [synOf_eq_zero_of_not_mem_range _ L a ha]
    exact Commute.zero_left _
  by_cases hb : b ∈ R.range
  swap
  · rw [synOf_eq_zero_of_not_mem_range _ R b hb]
    exact Commute.zero_right _
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  rw [← linear_measurement_fourier_inverse wZ L x, ← linear_measurement_fourier_inverse wX R y]
  apply commute_matrix_smul
  apply Commute.sum_left
  intro v _
  apply Commute.sum_right
  intro u _
  apply commute_matrix_smul
  have hp : trDot u.1 v.1 = 0 := by
    rw [trDot, (CL.mem_perp.mp v.2) u.1 (hLR u.2), map_zero]
  exact (wX_mul_wZ_of_eq u.1 v.1 hp).symm
end MIPRE.Introspection
