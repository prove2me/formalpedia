-- Prove2me | solution 1 for Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:36:54.527144+00:00
-- url     : https://prove2.me/submissions/f506bd8e-b7e5-4c8e-ab57-08230e4cce8c

/-
Copyright (c) 2026 Sirui Lu and the MIPStarRE contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE, with the
authors' permission. Vendored from https://github.com/LionSR/MIPStarRE
(commit 507e8122, 2026-08-25) by scripts/vendor-lidt.py; do not edit by hand.
Upstream path: MIPStarRE/Quantum/FiniteHilbert.lean
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Background/LIDT/MIPStarRE/Quantum/FiniteHilbert.lean (solution of Matrix.mul_conjTranspose_eq_one_of_orthonormal_rows);
   produced mechanically by prove2me/tools/gen.py, never edited by hand. -/

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! The uploaded declaration as `solution` (a root name declared inside the source's
namespace, so that names resolve as they do in the source). -/
namespace Matrix
open Module
set_option backward.isDefEq.respectTransparency false
theorem _root_.solution
    {𝕜 : Type*} [RCLike 𝕜]
    {m n : Type*} [DecidableEq m] [Fintype n]
    (row : m → EuclideanSpace 𝕜 n)
    (hrow : Orthonormal 𝕜 row) :
    (Matrix.of fun i j => row i j) * (Matrix.of fun i j => row i j)ᴴ =
      (1 : Matrix m m 𝕜) := by
  classical
  ext i j
  have horth := orthonormal_iff_ite.mp hrow j i
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
    Matrix.one_apply]
  calc
    ∑ k, row i k * star (row j k) = inner 𝕜 (row j) (row i) := by
      simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct]
    _ = if j = i then (1 : 𝕜) else 0 := horth
    _ = if i = j then (1 : 𝕜) else 0 := by
      by_cases hij : i = j <;> simp [hij, eq_comm]
end Matrix
