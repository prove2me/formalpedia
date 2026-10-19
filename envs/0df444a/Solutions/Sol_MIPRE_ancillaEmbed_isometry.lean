-- Prove2me | solution 1 for MIPRE.ancillaEmbed_isometry
-- status  : ACCEPTED   (prove)
-- author  : @thomasvidick
-- created : 2026-10-17T00:43:37.749272+00:00
-- url     : https://prove2.me/submissions/287d38ff-fbed-46d8-bcc7-38e98b90cb48

/-
Copyright (c) 2026 Thomas Vidick. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Vidick
-/
/- Generated for Prove2Me from vidick/MIPRE-formalization@70cbf1c, MIPRE/Foundations/Dilation.lean (solution of MIPRE.ancillaEmbed_isometry);
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
    [Fintype A] [DecidableEq A] (a₀ : A) :
    (ancillaEmbed d a₀)ᴴ * ancillaEmbed d a₀ = (1 : Matrix d d ℂ) := by
  ext j k
  rw [Matrix.mul_apply, Finset.sum_eq_single (k, a₀)]
  · by_cases h : j = k
    · subst h
      simp [ancillaEmbed]
    · simp [ancillaEmbed, Matrix.one_apply_ne h, Prod.mk.injEq, Ne.symm h]
  · intro p _ hp
    simp [ancillaEmbed, hp]
  · simp
end MIPRE
