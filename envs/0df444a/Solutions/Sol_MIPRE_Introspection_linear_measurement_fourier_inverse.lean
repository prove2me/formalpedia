-- Prove2me | solution 1 for MIPRE.Introspection.linear_measurement_fourier_inverse
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:37:43.8984+00:00
-- url     : https://prove2.me/submissions/6d1406c4-dc86-4c8b-9dce-09b221935227

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/LinearMeasurement.lean (solution of MIPRE.Introspection.linear_measurement_fourier_inverse);
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
import Theorems.Thm_MIPRE_Introspection_subspaceTrace_eq_zero_iff
import Theorems.Thm_MIPRE_Weyl_eq_sum_proj
import Theorems.Thm_MIPRE_Weyl_sum_sgn_linear
import Theorems.Thm_MIPRE_sgn_add

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_comm (x y : Fin n → F) : dotForm F n x y = dotForm F n y x := by
  simp only [dotForm_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_isRefl : (dotForm F n).IsRefl := fun x y h => by
  rw [dotForm_comm]; exact h
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
theorem dotForm_nondegenerate : (dotForm F n).Nondegenerate := by
  have key : ∀ x : Fin n → F, ∀ i : Fin n,
      dotForm F n x (Pi.single i 1) = x i := by
    intro x i
    rw [dotForm_apply, Finset.sum_eq_single i
      (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ i) h)]
    simp
  refine ⟨fun x hx => funext fun i => ?_, fun y hy => funext fun i => ?_⟩
  · rw [← key x i]; exact hx _
  · rw [← key y i, dotForm_comm]; exact hy _
end
end MIPRE.CL

namespace MIPRE.CL
section
open Finset Module Submodule LinearMap
variable {F : Type*} [Field F] {n : ℕ}
/-- **`lem:perp_perp`**, second part: the dot-product perp is an involution on subspaces, over
every field. -/
theorem perp_perp (S : Submodule F (Fin n → F)) : perp (perp S) = S :=
  LinearMap.BilinForm.orthogonal_orthogonal dotForm_nondegenerate dotForm_isRefl S
end
end MIPRE.CL

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*}
/-- In characteristic two a sum vanishes exactly when the two summands agree. -/
theorem add_eq_zero_iff (x y : F) : x + y = 0 ↔ x = y := by
  refine ⟨fun h => ?_, fun h => by rw [h, add_self]⟩
  calc x = x + y + y := (add_add_cancel x y).symm
    _ = y := by rw [h, zero_add]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*}
theorem add_eq_zero_iff_vec (a b : n → F) : a + b = 0 ↔ a = b := by
  refine ⟨fun h => funext fun l => (add_eq_zero_iff (a l) (b l)).mp (congrFun h l),
    fun h => by rw [h, add_self_vec]⟩
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_comm (a b : n → F) : trDot a b = trDot b a := by
  rw [trDot, trDot, Finset.sum_congr rfl fun l _ => mul_comm (a l) (b l)]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
variable {F : Type*} [Field F] [Algebra (ZMod 2) F] {n : Type*} [Fintype n]
theorem trDot_add_right (a b b' : n → F) : trDot a (b + b') = trDot a b + trDot a b' := by
  rw [trDot_comm, trDot_add_left, trDot_comm b a, trDot_comm b' a]
end
end MIPRE.Weyl

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
/-- Character cancellation on a subspace. -/
theorem sum_subspace_sign (S : Submodule F (Fin n → F)) (c : Fin n → F) :
    (∑ v : S, sgn (trDot v.1 c)) =
      if c ∈ CL.perp S then (Fintype.card S : ℂ) else 0 := by
  classical
  by_cases hc : c ∈ CL.perp S
  · rw [if_pos hc]
    have hzero := (subspaceTrace_eq_zero_iff S c).mpr hc
    have he (v : S) : trDot v.1 c = 0 := LinearMap.congr_fun hzero v
    simp only [he, sgn_zero, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · rw [if_neg hc]
    exact sum_sgn_linear (subspaceTrace S c) (mt (subspaceTrace_eq_zero_iff S c).mp hc)
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
theorem _root_.solution
    (w : (Fin n → F) → Matrix (Fin n → F) (Fin n → F) ℂ)
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (x : Fin n → F) :
    (Fintype.card (CL.perp L.ker) : ℂ)⁻¹ •
      ∑ v : CL.perp L.ker, sgn (trDot v.1 x) • w v.1 = synOf w L (L x) := by
  classical
  have hcard : (Fintype.card (CL.perp L.ker) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos (α := CL.perp L.ker)).ne'
  have he (z : Fin n → F) : x + z ∈ CL.perp (CL.perp L.ker) ↔ L z = L x := by
    rw [CL.perp_perp, LinearMap.mem_ker, map_add]
    exact (Weyl.add_eq_zero_iff_vec _ _).trans eq_comm
  rw [Finset.sum_congr rfl fun v (_ : v ∈ univ) => by
    rw [eq_sum_proj (w := w) v.1, Finset.smul_sum]]
  rw [Finset.sum_comm]
  simp_rw [smul_smul, ← sgn_add, ← trDot_add_right]
  rw [Finset.sum_congr rfl fun z (_ : z ∈ univ) => by
    rw [← Finset.sum_smul, sum_subspace_sign]]
  simp only [he]
  rw [Finset.smul_sum]
  unfold synOf
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : L z = L x
  · rw [if_pos hz, smul_smul, inv_mul_cancel₀ hcard, one_smul, if_pos hz]
  · rw [if_neg hz, zero_smul, smul_zero, if_neg hz]
end MIPRE.Introspection
