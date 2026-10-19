-- Prove2me | solution 1 for MIPRE.exists_isometry_of_povm
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-16T15:28:22.930621+00:00
-- url     : https://prove2.me/submissions/a8491b06-314c-40bb-af49-bd2f1010b6c8

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Dilation.lean (solution of MIPRE.exists_isometry_of_povm);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Definitions.Def_MIPRE_Foundations_Dilation

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace MIPRE
open Matrix
open scoped ComplexOrder Kronecker MatrixOrder
theorem _root_.solution {d A : Type*} [Fintype d] [DecidableEq d]
    [Fintype A] [DecidableEq A] {E : A → Matrix d d ℂ}
    (hpos : ∀ a, (E a).PosSemidef) (hsum : ∑ a, E a = 1) :
    ∃ V : Matrix (d × A) d ℂ, Vᴴ * V = 1 ∧
      ∀ a : A, Vᴴ * (ancillaProj d a * V) = E a := by
  classical
  choose K hK using fun a : A => CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (hpos a).nonneg
  have hKE : ∀ (a : A) (j k : d),
      E a j k = ∑ i : d, (starRingEnd ℂ) (K a i j) * K a i k := by
    intro a j k
    rw [hK a]
    simp [Matrix.mul_apply, Matrix.star_apply]
  set V : Matrix (d × A) d ℂ := Matrix.of fun p j => K p.2 p.1 j with hVdef
  refine ⟨V, ?_, ?_⟩
  · ext j k
    have h1 : (Vᴴ * V) j k = ∑ i : d, ∑ a : A, (starRingEnd ℂ) (K a i j) * K a i k := by
      simp [hVdef, Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_prod_type]
    rw [h1, Finset.sum_comm]
    have h2 : ∑ a : A, ∑ i : d, (starRingEnd ℂ) (K a i j) * K a i k = ∑ a : A, E a j k :=
      Finset.sum_congr rfl fun a _ => (hKE a j k).symm
    rw [h2, ← Matrix.sum_apply, hsum]
  · intro a
    ext j k
    have hAV : ∀ (p : d × A) (m : d),
        (ancillaProj d a * V) p m = if p.2 = a then K p.2 p.1 m else 0 := by
      intro p m
      rw [ancillaProj, Matrix.diagonal_mul, hVdef]
      split_ifs <;> simp
    have h3 : (Vᴴ * (ancillaProj d a * V)) j k
        = ∑ i : d, (starRingEnd ℂ) (K a i j) * K a i k := by
      rw [Matrix.mul_apply, Fintype.sum_prod_type]
      simp only [hAV, Matrix.conjTranspose_apply, mul_ite, mul_zero]
      simp [hVdef]
    rw [h3, ← hKE a j k]
end MIPRE
