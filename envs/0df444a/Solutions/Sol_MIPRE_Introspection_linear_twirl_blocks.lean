-- Prove2me | solution 1 for MIPRE.Introspection.linear_twirl_blocks
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T03:42:57.576076+00:00
-- url     : https://prove2.me/submissions/a518cba6-a854-4598-8056-3375cb220918

/-
Copyright (c) 2026 MIPRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Introspection/BlockTwirl.lean (solution of MIPRE.Introspection.linear_twirl_blocks);
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
import Mathlib.LinearAlgebra.Matrix.Kronecker
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
import Definitions.Def_MIPRE_Foundations_Introspection_BlockTwirl
import Theorems.Thm_MIPRE_Weyl_proj_wZ
import Theorems.Thm_MIPRE_Weyl_sum_sgn_trDot
import Theorems.Thm_MIPRE_sgn_add

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
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

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
/-- The trivial character sums to the dimension of the space. -/
theorem sum_sgn_trDot_zero :
    ∑ b : n → F, sgn (trDot b (0 : n → F)) = (Fintype.card (n → F) : ℂ) := by
  rw [Finset.sum_congr rfl fun b (_ : b ∈ univ) => by rw [trDot_zero_right, sgn_zero],
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
end
end MIPRE.Weyl

namespace MIPRE.Weyl
noncomputable section
open Finset Matrix
set_option linter.unusedSectionVars false
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : Type*} [Fintype n] [DecidableEq n]
theorem card_ne_zero : (Fintype.card (n → F) : ℂ) ≠ 0 := by
  have : 0 < Fintype.card (n → F) := Fintype.card_pos
  exact_mod_cast this.ne'
end
end MIPRE.Weyl

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
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
theorem amplify_wZ_mul_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (amplify (H := H) (wZ v) * M) (x, a) (y, b) = sgn (trDot v x) * M (x, a) (y, b) := by
  simp [amplify, Matrix.mul_apply, Matrix.kroneckerMap_apply, wZ_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
theorem mul_amplify_wZ_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (M * amplify (H := H) (wZ v)) (x, a) (y, b) = M (x, a) (y, b) * sgn (trDot v y) := by
  simp [amplify, Matrix.mul_apply, Matrix.kroneckerMap_apply, wZ_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
theorem amplify_wZ_conjugate_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (amplify (H := H) (wZ v) * M * amplify (H := H) (wZ v)) (x, a) (y, b) =
      sgn (trDot v (x + y)) * M (x, a) (y, b) := by
  rw [mul_amplify_wZ_entry, amplify_wZ_mul_entry, trDot_add_right, sgn_add]
  ring
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
/-- The full `Z` twirl removes precisely the off-diagonal blocks in the sampled register. -/
theorem dephaseZ_entry (x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    dephaseZ M (x, a) (y, b) = if x = y then M (x, a) (y, b) else 0 := by
  rw [dephaseZ, Matrix.smul_apply, Matrix.sum_apply]
  simp only [amplify_wZ_conjugate_entry, smul_eq_mul]
  rw [← Finset.sum_mul]
  by_cases hxy : x = y
  · subst y
    rw [Weyl.add_self_vec, sum_sgn_trDot_zero, if_pos rfl, ← mul_assoc,
      inv_mul_cancel₀ (Weyl.card_ne_zero (F := F) (n := Fin n)), one_mul]
  · have hne : x + y ≠ 0 := fun h => hxy ((Weyl.add_eq_zero_iff_vec x y).mp h)
    rw [sum_sgn_trDot hne, zero_mul, mul_zero, if_neg hxy]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
theorem amplify_wX_mul_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (amplify (H := H) (wX v) * M) (x, a) (y, b) = M (x + v, a) (y, b) := by
  have hx (z : Fin n → F) : x = z + v ↔ z = x + v := by
    constructor
    · intro h
      rw [h, Weyl.add_add_cancel_vec]
    · intro h
      rw [h, Weyl.add_add_cancel_vec]
  simp [amplify, Matrix.mul_apply, Matrix.kroneckerMap_apply, wX_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul, hx]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
theorem mul_amplify_wX_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (M * amplify (H := H) (wX v)) (x, a) (y, b) = M (x, a) (y + v, b) := by
  simp [amplify, Matrix.mul_apply, Matrix.kroneckerMap_apply, wX_apply,
    Fintype.sum_prod_type, Matrix.one_apply, mul_ite, ite_mul]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
theorem amplify_wX_conjugate_entry (v x y : Fin n → F) (a b : H)
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    (amplify (H := H) (wX v) * M * amplify (H := H) (wX v)) (x, a) (y, b) =
      M (x + v, a) (y + v, b) := by
  rw [mul_amplify_wX_entry, amplify_wX_mul_entry]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
/-- First dephasing, then averaging `X(K)`, leaves only the averaged diagonal blocks. -/
theorem averageX_dephaseZ_entry (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)
    (x y : Fin n → F) (a b : H) :
    averageX K (dephaseZ M) (x, a) (y, b) =
      if x = y then averagedBlock K M x a b else 0 := by
  rw [averageX, Matrix.smul_apply, Matrix.sum_apply]
  simp only [amplify_wX_conjugate_entry, dephaseZ_entry, add_left_inj, add_right_inj]
  by_cases hxy : x = y
  · subst y
    simp only [if_pos rfl]
    rw [averagedBlock, Matrix.smul_apply, Matrix.sum_apply]
    rfl
  · simp [hxy]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
/-- The averaged ancillary block is constant on each coset of the twirled subspace. -/
theorem averagedBlock_eq_of_sub_mem (K : Submodule F (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ)
    (x y : Fin n → F) (hxy : x - y ∈ K) : averagedBlock K M x = averagedBlock K M y := by
  let t : K := ⟨x - y, hxy⟩
  have hv (v : K) : y + (v + t).1 = x + v.1 := by
    change y + (v.1 + (x - y)) = x + v.1
    abel
  unfold averagedBlock
  congr 1
  apply Fintype.sum_equiv (Equiv.addRight t)
  intro v
  simp only [Equiv.coe_addRight, hv]
end
end MIPRE.Introspection

namespace MIPRE.Introspection
noncomputable section
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
theorem synOf_wZ_entry (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (a x y : Fin n → F) :
    synOf wZ L a x y = if x = y then (if L x = a then 1 else 0) else 0 := by
  rw [synOf, Matrix.sum_apply]
  simp only [proj_wZ, zProj_apply]
  by_cases hxy : x = y
  · subst y
    simp only [ite_true]
    by_cases ha : L x = a
    · rw [if_pos ha]
      rw [Finset.sum_eq_single_of_mem x (by simp [ha])]
      · simp
      · intro z hz hzx
        exact if_neg (Ne.symm hzx)
    · rw [if_neg ha]
      apply Finset.sum_eq_zero
      intro z hz
      apply if_neg
      intro hxz
      subst z
      exact ha (Finset.mem_filter.mp hz).2
  · simp [hxy]
end
end MIPRE.Introspection

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE.Introspection
open Finset Weyl Classical Matrix Kronecker
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Algebra (ZMod 2) F]
variable {n : ℕ} {H : Type*} [Fintype H] [DecidableEq H]
theorem _root_.solution (L : (Fin n → F) →ₗ[F] (Fin n → F))
    (M : Matrix ((Fin n → F) × H) ((Fin n → F) × H) ℂ) :
    averageX L.ker (dephaseZ M) =
      ∑ a : Fin n → F, synOf wZ L a ⊗ₖ averagedBlock L.ker M (linearPreimage L a) := by
  ext ⟨x, i⟩ ⟨y, j⟩
  rw [averageX_dephaseZ_entry, Matrix.sum_apply]
  simp only [Matrix.kroneckerMap_apply, synOf_wZ_entry]
  by_cases hxy : x = y
  · subst y
    simp only [if_pos rfl, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]
    have hker : x - linearPreimage L (L x) ∈ L.ker := by
      rw [LinearMap.mem_ker, map_sub, linearPreimage_image, sub_self]
    rw [averagedBlock_eq_of_sub_mem L.ker M _ _ hker]
  · simp [hxy]
end MIPRE.Introspection
