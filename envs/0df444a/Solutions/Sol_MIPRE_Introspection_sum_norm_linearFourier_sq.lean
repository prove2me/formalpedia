-- Prove2me | solution 1 for MIPRE.Introspection.sum_norm_linearFourier_sq
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:37:04.002163+00:00
-- url     : https://prove2.me/submissions/3fbcf647-d381-4f23-b7ed-30911a83dff3

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/CommutatorParseval.lean (solution of MIPRE.Introspection.sum_norm_linearFourier_sq);
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
import Definitions.Def_MIPRE_Foundations_Sign
import Definitions.Def_MIPRE_Foundations_LowDegree_SchwartzZippel
import Definitions.Def_MIPRE_Foundations_LowDegree_Anticomm
import Definitions.Def_MIPRE_Foundations_Weyl
import Definitions.Def_MIPRE_Foundations_Parseval
import Definitions.Def_MIPRE_Foundations_Introspection_LinearMeasurement
import Definitions.Def_MIPRE_Foundations_Introspection_CommutatorParseval
import Theorems.Thm_MIPRE_Introspection_subspaceTrace_eq_zero_iff
import Theorems.Thm_MIPRE_Weyl_sum_sgn_linear
import Theorems.Thm_MIPRE_dotProduct_star_self
import Theorems.Thm_MIPRE_sgn_add
import Theorems.Thm_MIPRE_star_sgn

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

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ}
theorem linearPreimage_image (L : (Fin n → F) →ₗ[F] (Fin n → F)) (x : Fin n → F) :
    L (linearPreimage L (L x)) = L x := by
  have hx : ∃ y, L y = L x := ⟨x, rfl⟩
  rw [linearPreimage, dif_pos hx]
  exact hx.choose_spec
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Matrix Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]
/-- A chosen preimage maps to its target whenever the target lies in the range. -/
theorem linearPreimage_mem_range (L : (Fin n → F) →ₗ[F] (Fin n → F))
    {y : Fin n → F} (hy : y ∈ L.range) : L (linearPreimage L y) = y := by
  obtain ⟨x, rfl⟩ := hy
  exact linearPreimage_image L x
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Matrix Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]
/-- Distinct nonempty fibres have orthogonal characters on the kernel's perpendicular. -/
theorem sum_linear_fiber_sign (L : (Fin n → F) →ₗ[F] (Fin n → F))
    {a b : Fin n → F} (ha : a ∈ L.range) (hb : b ∈ L.range) :
    (∑ v : CL.perp L.ker, sgn (trDot v.1 (linearPreimage L a + linearPreimage L b))) =
      if a = b then (Fintype.card (CL.perp L.ker) : ℂ) else 0 := by
  rw [sum_subspace_sign, CL.perp_perp]
  have h : linearPreimage L a + linearPreimage L b ∈ L.ker ↔ a = b := by
    rw [LinearMap.mem_ker, map_add, linearPreimage_mem_range L ha,
      linearPreimage_mem_range L hb, Weyl.add_eq_zero_iff_vec]
  simp only [h]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Weyl Matrix Classical
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {N : Type*} [Fintype N]
theorem _root_.solution
    (L : (Fin n → F) →ₗ[F] (Fin n → F)) (T : (Fin n → F) → (N → ℂ))
    (hT : ∀ y, y ∉ L.range → T y = 0) :
    (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ *
        (∑ v : CL.perp L.ker, ‖evec (∑ y : Fin n → F,
          sgn (trDot v.1 (linearPreimage L y)) • T y)‖ ^ 2) =
      ∑ y : Fin n → F, ‖evec (T y)‖ ^ 2 := by
  let G (v : CL.perp L.ker) : N → ℂ :=
    ∑ y : Fin n → F, sgn (trDot v.1 (linearPreimage L y)) • T y
  have hexpand (v : CL.perp L.ker) : star (G v) ⬝ᵥ G v =
      ∑ a : Fin n → F, ∑ b : Fin n → F,
        sgn (trDot v.1 (linearPreimage L a + linearPreimage L b)) *
          (star (T a) ⬝ᵥ T b) := by
    dsimp only [G]
    rw [star_sum, sum_dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [dotProduct_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [star_smul, star_sgn, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      smul_eq_mul, trDot_add_right, sgn_add, mul_assoc]
  have hdiag (a b : Fin n → F) :
      (∑ v : CL.perp L.ker,
        sgn (trDot v.1 (linearPreimage L a + linearPreimage L b))) *
          (star (T a) ⬝ᵥ T b) =
      if a = b then (Fintype.card (CL.perp L.ker) : ℂ) * (star (T a) ⬝ᵥ T a)
      else 0 := by
    by_cases ha : a ∈ L.range
    · by_cases hb : b ∈ L.range
      · rw [sum_linear_fiber_sign L ha hb]
        split_ifs with hab
        · subst b; rfl
        · exact zero_mul _
      · rw [hT b hb]
        by_cases hab : a = b
        · exact False.elim (hb (hab ▸ ha))
        · simp [hab]
    · rw [hT a ha]
      simp
  have hsum : (∑ v : CL.perp L.ker, star (G v) ⬝ᵥ G v) =
      (Fintype.card (CL.perp L.ker) : ℂ) * ∑ a : Fin n → F, star (T a) ⬝ᵥ T a := by
    simp_rw [hexpand]
    rw [Finset.sum_comm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, hdiag]
    simp
  have hreal : (∑ v : CL.perp L.ker, ‖evec (G v)‖ ^ 2) =
      (Fintype.card (CL.perp L.ker) : ℝ) * ∑ a : Fin n → F, ‖evec (T a)‖ ^ 2 := by
    simp_rw [dotProduct_star_self] at hsum
    exact_mod_cast hsum
  change (Fintype.card (CL.perp L.ker) : ℝ)⁻¹ * (∑ v, ‖evec (G v)‖ ^ 2) = _
  rw [hreal, ← mul_assoc, inv_mul_cancel₀, one_mul]
  exact_mod_cast (Fintype.card_pos (α := CL.perp L.ker)).ne'
end MIPRE.Introspection
