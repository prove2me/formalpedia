-- Prove2me | solution 1 for MIPRE.exists_projective_dilation
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:29:52.976177+00:00
-- url     : https://prove2.me/submissions/8e7c9f78-870f-4e0f-9371-2c41f27de3ae

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Dilation.lean (solution of MIPRE.exists_projective_dilation);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_Dilation
import Theorems.Thm_MIPRE_exists_isometry_of_povm
import Theorems.Thm_MIPRE_exists_unitary_extending

/-! Helper declarations, pasted verbatim from the source modules with their
namespace and `open` context, each used only by proofs, interleaved with the
attribute commands of those modules at their source positions. -/
namespace MIPRE
section
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
theorem ancillaProj_conjTranspose {d A : Type*} [DecidableEq d] [DecidableEq A] (a : A) :
    (ancillaProj d a)ᴴ = ancillaProj d a := by
  rw [ancillaProj, Matrix.diagonal_conjTranspose]
  congr 1
  funext p
  simp only [Pi.star_apply]
  split_ifs <;> simp
end
end MIPRE

namespace MIPRE
section
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
theorem ancillaProj_mul_self {d A : Type*} [Fintype d] [DecidableEq d] [Fintype A]
    [DecidableEq A] (a : A) :
    ancillaProj d a * ancillaProj d a = ancillaProj d a := by
  rw [ancillaProj, Matrix.diagonal_mul_diagonal]
  congr 1
  funext p
  split_ifs <;> simp
end
end MIPRE

namespace MIPRE
section
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
theorem sum_ancillaProj {d A : Type*} [DecidableEq d] [Fintype A] [DecidableEq A] :
    ∑ a : A, ancillaProj d a = (1 : Matrix (d × A) (d × A) ℂ) := by
  ext p q
  rw [Matrix.sum_apply]
  by_cases h : p = q
  · subst h
    simp [ancillaProj, Matrix.one_apply_eq]
  · simp [ancillaProj, Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
end
end MIPRE

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
theorem _root_.solution {d A X : Type*} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] (a₀ : A) {E : X → A → Matrix d d ℂ}
    (hpos : ∀ x a, (E x a).PosSemidef) (hsum : ∀ x, ∑ a, E x a = 1) :
    ∃ P : X → A → Matrix (d × A) (d × A) ℂ,
      (∀ x a, star (P x a) = P x a) ∧
      (∀ x a, P x a * P x a = P x a) ∧
      (∀ x, ∑ a, P x a = 1) ∧
      (∀ x a, (ancillaEmbed d a₀)ᴴ * (P x a * ancillaEmbed d a₀) = E x a) := by
  classical
  choose V hViso hVE using fun x : X => exists_isometry_of_povm (hpos x) (hsum x)
  choose U hUiso hUV using fun x : X => exists_unitary_extending a₀ (hViso x)
  have hUU : ∀ x, U x * (U x)ᴴ = 1 := fun x => mul_eq_one_comm.mp (hUiso x)
  refine ⟨fun x a => (U x)ᴴ * (ancillaProj d a * U x), ?_, ?_, ?_, ?_⟩
  · intro x a
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, ancillaProj_conjTranspose, Matrix.mul_assoc]
  · intro x a
    have h : (U x)ᴴ * (ancillaProj d a * U x) * ((U x)ᴴ * (ancillaProj d a * U x))
        = (U x)ᴴ * (ancillaProj d a * (U x * (U x)ᴴ * (ancillaProj d a * U x))) := by
      simp only [Matrix.mul_assoc]
    rw [h, hUU, Matrix.one_mul, ← Matrix.mul_assoc (ancillaProj d a) (ancillaProj d a) (U x),
      ancillaProj_mul_self]
  · intro x
    have h : ∑ a : A, (U x)ᴴ * (ancillaProj d a * U x)
        = (U x)ᴴ * ((∑ a : A, ancillaProj d a) * U x) := by
      rw [Finset.sum_mul, Finset.mul_sum]
    rw [h, sum_ancillaProj, Matrix.one_mul, hUiso]
  · intro x a
    have h : (ancillaEmbed d a₀)ᴴ * ((U x)ᴴ * (ancillaProj d a * U x) * ancillaEmbed d a₀)
        = (U x * ancillaEmbed d a₀)ᴴ * (ancillaProj d a * (U x * ancillaEmbed d a₀)) := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    rw [h, hUV, hVE]
end MIPRE
