-- Prove2me | solution 1 for MIPRE.Introspection.subspaceTrace_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:05:02.025668+00:00
-- url     : https://prove2.me/submissions/b8f06fbb-a4b2-4d3f-9116-c5912c596e2d

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/LinearMeasurement.lean (solution of MIPRE.Introspection.subspaceTrace_eq_zero_iff);
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
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
/-- Scaling one argument of the pairing pulls the scalar out. -/
theorem trDot_smul (r : F) (v e : n → F) :
    trDot (r • v) e = Algebra.trace (ZMod 2) F (r * dotF v e) := by
  rw [trDot, dotF, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun l _ => by rw [Pi.smul_apply, smul_eq_mul, mul_assoc]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {w : (n → F) → Matrix (n → F) (n → F) ℂ}
theorem trMulL_ne_zero {x : F} (hx : x ≠ 0) : trMulL x ≠ 0 := by
  obtain ⟨y, hy⟩ := Algebra.trace_surjective (ZMod 2) F 1
  intro h
  have h0 : Algebra.trace (ZMod 2) F ((y / x) * x) = 0 := by
    have := congrFun (congrArg (fun t : F →ₗ[ZMod 2] ZMod 2 => t.toFun) h) (y / x)
    simpa [trMulL] using this
  rw [div_mul_cancel₀ _ hx, hy] at h0
  exact one_ne_zero h0
end
end MIPRE.Weyl

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
theorem _root_.solution (S : Submodule F (Fin n → F)) (c : Fin n → F) :
    subspaceTrace S c = 0 ↔ c ∈ CL.perp S := by
  rw [CL.mem_perp]
  constructor
  · intro h y hy
    by_contra hne
    apply trMulL_ne_zero (x := dotF y c) hne
    ext r
    change Algebra.trace (ZMod 2) F (r * dotF y c) = 0
    have he := LinearMap.congr_fun h ⟨r • y, S.smul_mem r hy⟩
    simpa only [subspaceTrace_apply, LinearMap.zero_apply, trDot_smul] using he
  · intro h
    ext v
    change Algebra.trace (ZMod 2) F (∑ i, v.1 i * c i) = 0
    rw [h v.1 v.2, map_zero]
end MIPRE.Introspection
